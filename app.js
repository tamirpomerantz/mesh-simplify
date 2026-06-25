import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { OBJLoader } from 'three/addons/loaders/OBJLoader.js';
import { OBJExporter } from 'three/addons/exporters/OBJExporter.js';
import * as BufferGeometryUtils from 'three/addons/utils/BufferGeometryUtils.js';
import { MeshoptSimplifier } from 'https://unpkg.com/meshoptimizer/meshopt_simplifier.js';

// --- Application State ---
let scene, camera, renderer, controls;
let gridHelper, axesHelper;
let originalGroup = null;      // Holds the original parsed & normalized model
let simplifiedGroup = null;    // Holds the currently rendered simplified model
let wireframeOverlay = null;   // Holds the wireframe line segments overlay
let isWasmReady = false;

// Normalization transform cache (to restore original coordinates on export)
let normalizationScale = 1.0;
let normalizationOffset = new THREE.Vector3();
let originalFileName = "mesh.obj";

// Textures State
const loadedTextures = {
    color: null,
    normal: null,
    roughness: null,
    ao: null
};
let textureObjectURLs = [];

// UV Projection & Editor State
let activeWeldedGeom = null; // Caches the active welded geometry for UV projection references
const uvOptions = {
    mode: 'original', // 'original', 'planar-front', 'planar-top', 'spherical', 'cylindrical'
    scale: 1.0
};

const editorUVTransforms = {
    scaleU: 1.0,
    scaleV: 1.0,
    offsetU: 0.0,
    offsetV: 0.0,
    rotation: 0.0,
    flipV: false
};

// Hierarchy, Pieces and Islands Selection States
let selectedItem = null;        // Currently selected item: { type: 'piece'/'island', meshName: string, islandId: number }
let hoveredItem = null;         // Currently hovered item in list: { type: 'piece'/'island', meshName: string, islandId: number }
const itemTransforms = new Map(); // Key -> { scaleU, scaleV, offsetU, offsetV, rotation, visible }
let piecesHierarchy = [];       // Cache of Pieces and their UV Islands: [ { meshName, meshRef, islands: [ [triIdxs], ... ] } ]

// 3D Raycasting globals for bidirectional viewport interaction
const raycaster = new THREE.Raycaster();
const mouse3D = new THREE.Vector2();

// 2D Canvas Mouse Dragging State
let isDraggingUV = false;
let dragStartU = 0;
let dragStartV = 0;
let dragStartOffsetU = 0;
let dragStartOffsetV = 0;

// Algorithmic & visual options
const options = {
    ratio: 0.5,             // 50% target face count
    lockBorders: true,      // Lock boundaries to prevent seams
    regularize: false,      // Regularize triangle shape
    targetError: 1.0,       // Max allowed shape deviation error (relative)
    viewMode: 'solid',      // 'solid', 'both', 'wire'
    shadingMode: 'smooth',  // 'smooth', 'flat'
    materialStyle: 'clay'   // 'clay', 'metallic', 'xray'
};

// Material Cache
let materials = {};

// Performance / debouncing state
let lastSimplificationTime = 0;
let debounceTimeout = null;

// --- Initialize App ---
init();

function init() {
    setupThreeJS();
    setupMaterials();
    setupEventListeners();
    initMeshoptimizer();
    animate();
}

// --- WebGL / Three.js Viewport Setup ---
function setupThreeJS() {
    const container = document.getElementById('canvas-container');
    const width = container.clientWidth;
    const height = container.clientHeight;

    // Scene
    scene = new THREE.Scene();
    scene.background = null; // Background is styled via CSS gradient on viewport container

    // Camera
    camera = new THREE.PerspectiveCamera(45, width / height, 0.1, 1000);
    camera.position.set(10, 8, 12);

    // Renderer
    renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true, preserveDrawingBuffer: true });
    renderer.setSize(width, height);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    renderer.shadowMap.enabled = true;
    renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    container.appendChild(renderer.domElement);

    // Controls
    controls = new OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.dampingFactor = 0.05;
    controls.maxPolarAngle = Math.PI / 2 + 0.1; // allow looking slightly below floor

    // Lights
    const ambientLight = new THREE.AmbientLight(0xffffff, 0.45);
    scene.add(ambientLight);

    // Three-point lighting for CAD/Sculpture feel
    const keyLight = new THREE.DirectionalLight(0xffffff, 0.85);
    keyLight.position.set(15, 20, 10);
    keyLight.castShadow = true;
    keyLight.shadow.mapSize.width = 2048;
    keyLight.shadow.mapSize.height = 2048;
    keyLight.shadow.bias = -0.0005;
    scene.add(keyLight);

    const fillLight = new THREE.DirectionalLight(0x90b0ff, 0.4);
    fillLight.position.set(-15, 10, -10);
    scene.add(fillLight);

    const rimLight = new THREE.DirectionalLight(0xffd8b0, 0.25);
    rimLight.position.set(0, -10, 15);
    scene.add(rimLight);

    // Helpers
    gridHelper = new THREE.GridHelper(20, 20, 0x00d2ff, 0x243042);
    gridHelper.position.y = 0;
    scene.add(gridHelper);

    axesHelper = new THREE.AxesHelper(3);
    axesHelper.position.set(-9.8, 0.01, -9.8);
    // Style axes helper colors
    const axesColors = axesHelper.geometry.attributes.color;
    // R, G, B colors for X, Y, Z axes
    scene.add(axesHelper);

    // Resize Handler
    window.addEventListener('resize', onWindowResize);
}

function onWindowResize() {
    const container = document.getElementById('canvas-container');
    camera.aspect = container.clientWidth / container.clientHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(container.clientWidth, container.clientHeight);
}

function animate() {
    requestAnimationFrame(animate);
    controls.update();
    renderer.render(scene, camera);
}

// --- Materials System ---
function setupMaterials() {
    // 1. Clay Material (Matte, beautiful structure)
    materials.clay = new THREE.MeshStandardMaterial({
        color: 0xe0e0e0,
        roughness: 0.6,
        metalness: 0.1,
        side: THREE.DoubleSide,
        polygonOffset: true,
        polygonOffsetFactor: 1,
        polygonOffsetUnits: 1
    });

    // 2. Metallic Material (High sheen, reflection contours)
    materials.metallic = new THREE.MeshStandardMaterial({
        color: 0x99aab8,
        roughness: 0.18,
        metalness: 0.92,
        side: THREE.DoubleSide,
        polygonOffset: true,
        polygonOffsetFactor: 1,
        polygonOffsetUnits: 1
    });

    // 3. Hologram Material (Cyberpunk glowing mesh)
    materials.xray = new THREE.MeshBasicMaterial({
        color: 0x00d2ff,
        transparent: true,
        opacity: 0.25,
        blending: THREE.AdditiveBlending,
        side: THREE.DoubleSide,
        depthWrite: false,
        polygonOffset: true,
        polygonOffsetFactor: 1,
        polygonOffsetUnits: 1
    });

    // 4. Textured Material (For rendering image texture maps)
    materials.textured = new THREE.MeshStandardMaterial({
        color: 0xffffff,
        roughness: 1.0,
        metalness: 1.0,
        side: THREE.DoubleSide,
        polygonOffset: true,
        polygonOffsetFactor: 1,
        polygonOffsetUnits: 1
    });
}

// --- Meshoptimizer WASM Loader ---
function initMeshoptimizer() {
    const dot = document.getElementById('wasm-status-dot');
    const text = document.getElementById('wasm-status-text');

    if (typeof MeshoptSimplifier === 'undefined') {
        dot.className = "status-dot error";
        text.innerText = "WASM LOADING FAILED";
        console.error("MeshoptSimplifier is not available in the module scope.");
        return;
    }

    MeshoptSimplifier.ready.then(() => {
        isWasmReady = true;
        dot.className = "status-dot success";
        text.innerText = "WASM ONLINE (MESHOPT 1.1)";
        console.log("Meshoptimizer WebAssembly Module Loaded successfully.");
    }).catch((err) => {
        dot.className = "status-dot error";
        text.innerText = "WASM BOOT ERROR";
        console.error("Failed to initialize Meshopt Wasm module:", err);
    });
}

// --- Event Listeners and UI Interactions ---
function setupEventListeners() {
    // Drag & Drop File Handlers
    const dropZone = document.getElementById('drop-zone');
    const fileInput = document.getElementById('file-input');

    dropZone.addEventListener('dragover', (e) => {
        e.preventDefault();
        dropZone.classList.add('dragover');
    });

    dropZone.addEventListener('dragleave', () => {
        dropZone.classList.remove('dragover');
    });

    dropZone.addEventListener('drop', (e) => {
        e.preventDefault();
        dropZone.classList.remove('dragover');
        if (e.dataTransfer.files.length > 0) {
            handleMultipleFiles(e.dataTransfer.files);
        }
    });

    fileInput.addEventListener('change', () => {
        if (fileInput.files.length > 0) {
            handleMultipleFiles(fileInput.files);
        }
    });

    // Ratio Slider Live Update
    const ratioSlider = document.getElementById('ratio-slider');
    const ratioValue = document.getElementById('ratio-value');
    
    ratioSlider.addEventListener('input', () => {
        const pct = ratioSlider.value;
        ratioValue.innerText = `${pct}%`;
        options.ratio = pct / 100;
        
        // Dynamic adaptive simplification trigger
        // If the last simplification took less than 30ms, run in real-time.
        // Otherwise, debounce to avoid rendering lag.
        if (lastSimplificationTime < 35) {
            triggerSimplification();
        } else {
            // Debounce
            if (debounceTimeout) clearTimeout(debounceTimeout);
            debounceTimeout = setTimeout(triggerSimplification, 80);
        }
    });

    ratioSlider.addEventListener('change', () => {
        // Enforce final simplification on release
        triggerSimplification();
    });

    // View Mode Radios
    const viewRadios = document.getElementsByName('view-mode');
    viewRadios.forEach(radio => {
        radio.addEventListener('change', () => {
            options.viewMode = radio.value;
            updateDisplayMode();
        });
    });

    // Shading Mode Radios
    const shadeRadios = document.getElementsByName('shade-mode');
    shadeRadios.forEach(radio => {
        radio.addEventListener('change', () => {
            options.shadingMode = radio.value;
            document.getElementById('hud-shading').innerText = options.shadingMode === 'smooth' ? 'Smooth' : 'Flat';
            updateShadingMode();
        });
    });

    // Material Radios
    const matRadios = document.getElementsByName('mat-style');
    matRadios.forEach(radio => {
        radio.addEventListener('change', () => {
            options.materialStyle = radio.value;
            updateMaterialStyle();
        });
    });

    // Advanced Constraints Switches
    document.getElementById('lock-borders-chk').addEventListener('change', (e) => {
        options.lockBorders = e.target.checked;
        triggerSimplification();
    });

    document.getElementById('regularize-chk').addEventListener('change', (e) => {
        options.regularize = e.target.checked;
        triggerSimplification();
    });

    const errorSlider = document.getElementById('error-slider');
    const errorValue = document.getElementById('error-value');
    errorSlider.addEventListener('input', () => {
        const val = errorSlider.value / 100;
        errorValue.innerText = val === 1.0 ? '1.00 (Max)' : val.toFixed(2);
        options.targetError = val;
    });
    errorSlider.addEventListener('change', () => {
        triggerSimplification();
    });

    // Viewport HUD & Toolbar controls
    document.getElementById('ctrl-focus').addEventListener('click', fitCameraToModel);
    
    const gridBtn = document.getElementById('ctrl-grid');
    gridBtn.addEventListener('click', () => {
        gridHelper.visible = !gridHelper.visible;
        axesHelper.visible = gridHelper.visible;
        gridBtn.classList.toggle('active', gridHelper.visible);
    });

    document.getElementById('ctrl-top').addEventListener('click', () => setCameraPreset('top'));
    document.getElementById('ctrl-front').addEventListener('click', () => setCameraPreset('front'));
    document.getElementById('ctrl-side').addEventListener('click', () => setCameraPreset('side'));

    // Export and Reset buttons
    document.getElementById('download-btn').addEventListener('click', exportModel);
    document.getElementById('reset-btn').addEventListener('click', resetUploader);

    // UV Mapping Tool & Editor Event Listeners
    const uvModeSelect = document.getElementById('uv-mode-select');
    const uvScaleSlider = document.getElementById('uv-scale-slider');
    const uvScaleVal = document.getElementById('uv-scale-val');
    const uvApplyBtn = document.getElementById('uv-apply-btn');
    
    // Collapsible Drawer Controls
    const uvDrawer = document.getElementById('uv-editor-drawer');
    const sliderSU = document.getElementById('editor-scale-u');
    const sliderSV = document.getElementById('editor-scale-v');
    const sliderOU = document.getElementById('editor-offset-u');
    const sliderOV = document.getElementById('editor-offset-v');
    const sliderRot = document.getElementById('editor-rotation');

    const bubbleSU = document.getElementById('val-scale-u');
    const bubbleSV = document.getElementById('val-scale-v');
    const bubbleOU = document.getElementById('val-offset-u');
    const bubbleOV = document.getElementById('val-offset-v');
    const bubbleRot = document.getElementById('val-rotation');

    // Toggle Drawer Open/Close
    document.getElementById('toggle-uv-editor-btn').addEventListener('click', () => {
        uvDrawer.classList.add('open');
        setTimeout(drawUVWireframe, 100);
    });

    document.getElementById('close-uv-drawer-btn').addEventListener('click', () => {
        uvDrawer.classList.remove('open');
        selectedItem = null;
        rebuildHierarchyUI();
    });

    uvModeSelect.addEventListener('change', (e) => {
        uvOptions.mode = e.target.value;
        if (simplifiedGroup) {
            console.log(`UV Projection Mode changed to: ${uvOptions.mode}. Re-simplifying to apply...`);
            triggerSimplification();
        }
    });

    uvScaleSlider.addEventListener('input', () => {
        const val = uvScaleSlider.value / 100;
        uvScaleVal.innerText = `${val.toFixed(1)}x`;
        uvOptions.scale = val;
        
        if (simplifiedGroup) {
            applyUVProjectionToGroup(simplifiedGroup);
            drawUVWireframe();
        }
    });

    uvApplyBtn.addEventListener('click', () => {
        console.log("Resetting UV projection to original coordinates.");
        uvModeSelect.value = 'original';
        uvOptions.mode = 'original';
        uvScaleSlider.value = 100;
        uvScaleVal.innerText = '1.0x';
        uvOptions.scale = 1.0;
        if (simplifiedGroup) {
            triggerSimplification();
        }
    });

    // UV Editor Transforms Update Helper (applies to SELECTED Piece or Island)
    function updateEditorTransforms() {
        if (!selectedItem) {
            console.warn("No Piece or Island selected to transform.");
            return;
        }

        const key = selectedItem.type === 'piece' 
            ? `piece:${selectedItem.meshName}` 
            : `island:${selectedItem.meshName}:${selectedItem.islandId}`;
            
        let transform = itemTransforms.get(key);
        if (!transform) {
            transform = { scaleU: 1.0, scaleV: 1.0, offsetU: 0.0, offsetV: 0.0, rotation: 0.0, visible: true };
            itemTransforms.set(key, transform);
        }

        transform.scaleU = sliderSU.value / 100;
        transform.scaleV = sliderSV.value / 100;
        transform.offsetU = sliderOU.value / 100;
        transform.offsetV = sliderOV.value / 100;
        transform.rotation = parseFloat(sliderRot.value);

        bubbleSU.innerText = `${transform.scaleU.toFixed(1)}x`;
        bubbleSV.innerText = `${transform.scaleV.toFixed(1)}x`;
        bubbleOU.innerText = `${transform.offsetU.toFixed(2)}`;
        bubbleOV.innerText = `${transform.offsetV.toFixed(2)}`;
        bubbleRot.innerText = `${transform.rotation.toFixed(0)}°`;

        if (simplifiedGroup) {
            applyUVProjectionToGroup(simplifiedGroup);
            drawUVWireframe();
        }
    }

    // Bind input events for ultra-smooth real-time viewport feedback
    sliderSU.addEventListener('input', updateEditorTransforms);
    sliderSV.addEventListener('input', updateEditorTransforms);
    sliderOU.addEventListener('input', updateEditorTransforms);
    sliderOV.addEventListener('input', updateEditorTransforms);
    sliderRot.addEventListener('input', updateEditorTransforms);

    // Flip V Axis for Selected Item
    document.getElementById('editor-flip-v-btn').addEventListener('click', () => {
        if (!selectedItem) return;
        const key = selectedItem.type === 'piece' 
            ? `piece:${selectedItem.meshName}` 
            : `island:${selectedItem.meshName}:${selectedItem.islandId}`;
            
        let transform = itemTransforms.get(key);
        if (!transform) {
            transform = { scaleU: 1.0, scaleV: 1.0, offsetU: 0.0, offsetV: 0.0, rotation: 0.0, visible: true };
            itemTransforms.set(key, transform);
        }
        transform.flipV = !transform.flipV;
        console.log(`UV V-Axis flipped for ${key} to: ${transform.flipV}`);
        
        if (simplifiedGroup) {
            applyUVProjectionToGroup(simplifiedGroup);
            drawUVWireframe();
        }
    });

    // Reset Selected Item transforms
    document.getElementById('editor-reset-btn').addEventListener('click', () => {
        if (!selectedItem) return;
        const key = selectedItem.type === 'piece' 
            ? `piece:${selectedItem.meshName}` 
            : `island:${selectedItem.meshName}:${selectedItem.islandId}`;
            
        console.log(`Resetting transforms for ${key}`);
        
        sliderSU.value = 100;
        sliderSV.value = 100;
        sliderOU.value = 0;
        sliderOV.value = 0;
        sliderRot.value = 0;
        
        let transform = itemTransforms.get(key);
        if (transform) {
            transform.scaleU = 1.0;
            transform.scaleV = 1.0;
            transform.offsetU = 0.0;
            transform.offsetV = 0.0;
            transform.rotation = 0.0;
            transform.flipV = false;
        }
        updateEditorTransforms();
    });

    // --- Interactive 2D UV Canvas Mouse Dragging ---
    const uvCanvas = document.getElementById('uv-canvas');
    
    uvCanvas.addEventListener('mousedown', (e) => {
        if (!simplifiedGroup) return;
        
        const rect = uvCanvas.getBoundingClientRect();
        const mx = e.clientX - rect.left;
        const my = e.clientY - rect.top;
        
        // Convert canvas pixels to UV coordinate space [0, 1] (flipping Y)
        const clickU = mx / rect.width;
        const clickV = 1 - (my / rect.height);
        
        console.log(`Canvas clicked at UV: (${clickU.toFixed(3)}, ${clickV.toFixed(3)})`);
        
        // 1. If we ALREADY have a selected item, drag it directly!
        if (selectedItem) {
            const key = selectedItem.type === 'piece' 
                ? `piece:${selectedItem.meshName}` 
                : `island:${selectedItem.meshName}:${selectedItem.islandId}`;
                
            let transform = itemTransforms.get(key);
            if (!transform) {
                transform = { scaleU: 1.0, scaleV: 1.0, offsetU: 0.0, offsetV: 0.0, rotation: 0.0, visible: true, flipV: false };
                itemTransforms.set(key, transform);
            }
            
            isDraggingUV = true;
            dragStartU = clickU;
            dragStartV = clickV;
            dragStartOffsetU = transform.offsetU;
            dragStartOffsetV = transform.offsetV;
            return;
        }
        
        // 2. If nothing is selected, run 2D Raycast Hit-Test to find which UV Island was clicked
        const hit = getIslandAtUV(clickU, clickV);
        if (hit) {
            console.log(`UV Editor Selected: Piece "${hit.meshName}", Island #${hit.islandId}`);
            
            // Set Selection State
            selectedItem = {
                type: 'island',
                meshName: hit.meshName,
                islandId: hit.islandId
            };
            
            // Highlight in tree UI
            rebuildHierarchyUI();
            
            // Sync sliders to this island's transform
            const key = `island:${hit.meshName}:${hit.islandId}`;
            let transform = itemTransforms.get(key);
            if (!transform) {
                transform = { scaleU: 1.0, scaleV: 1.0, offsetU: 0.0, offsetV: 0.0, rotation: 0.0, visible: true, flipV: false };
                itemTransforms.set(key, transform);
            }
            
            sliderSU.value = transform.scaleU * 100;
            sliderSV.value = transform.scaleV * 100;
            sliderOU.value = transform.offsetU * 100;
            sliderOV.value = transform.offsetV * 100;
            sliderRot.value = transform.rotation;
            
            bubbleSU.innerText = `${transform.scaleU.toFixed(1)}x`;
            bubbleSV.innerText = `${transform.scaleV.toFixed(1)}x`;
            bubbleOU.innerText = `${transform.offsetU.toFixed(2)}`;
            bubbleOV.innerText = `${transform.offsetV.toFixed(2)}`;
            bubbleRot.innerText = `${transform.rotation.toFixed(0)}°`;
            
            // Redraw viewport with highlight
            drawUVWireframe();
            
            // Initialize Mouse Dragging Offset
            isDraggingUV = true;
            dragStartU = clickU;
            dragStartV = clickV;
            dragStartOffsetU = transform.offsetU;
            dragStartOffsetV = transform.offsetV;
        }
    });

    uvCanvas.addEventListener('mousemove', (e) => {
        if (!isDraggingUV || !selectedItem) return;
        
        const rect = uvCanvas.getBoundingClientRect();
        const mx = e.clientX - rect.left;
        const my = e.clientY - rect.top;
        
        const currentU = mx / rect.width;
        const currentV = 1 - (my / rect.height);
        
        // Calculate drag delta in UV coordinate units
        const du = currentU - dragStartU;
        const dv = currentV - dragStartV;
        
        const key = selectedItem.type === 'piece' 
            ? `piece:${selectedItem.meshName}` 
            : `island:${selectedItem.meshName}:${selectedItem.islandId}`;
            
        const transform = itemTransforms.get(key);
        if (transform) {
            transform.offsetU = dragStartOffsetU + du;
            transform.offsetV = dragStartOffsetV + dv;
            
            // Sync slider handles in the UI
            sliderOU.value = transform.offsetU * 100;
            sliderOV.value = transform.offsetV * 100;
            bubbleOU.innerText = `${transform.offsetU.toFixed(2)}`;
            bubbleOV.innerText = `${transform.offsetV.toFixed(2)}`;
            
            // Render updates in real-time
            applyUVProjectionToGroup(simplifiedGroup);
            drawUVWireframe();
        }
    });

    const stopDragging = () => {
        if (isDraggingUV) {
            isDraggingUV = false;
            console.log("Finished UV dragging.");
        }
    };

    uvCanvas.addEventListener('mouseup', stopDragging);
    uvCanvas.addEventListener('mouseleave', stopDragging);

    // --- Interactive 3D Viewport Raycasting (Hover & Click Selection) ---
    renderer.domElement.addEventListener('mousemove', (e) => {
        const uvDrawer = document.getElementById('uv-editor-drawer');
        if (!uvDrawer || !uvDrawer.classList.contains('open') || !simplifiedGroup) return;

        // If dragging camera/controls, don't trigger hover highlights
        if (e.buttons > 0) return;

        const rect = renderer.domElement.getBoundingClientRect();
        mouse3D.x = ((e.clientX - rect.left) / rect.width) * 2 - 1;
        mouse3D.y = -((e.clientY - rect.top) / rect.height) * 2 + 1;

        raycaster.setFromCamera(mouse3D, camera);
        const intersects = raycaster.intersectObjects(simplifiedGroup.children, true);

        if (intersects.length > 0) {
            const intersect = intersects[0];
            const mesh = intersect.object;
            const geom = mesh.geometry;
            
            if (geom && geom.userData && geom.userData.islandIds) {
                const islandIds = geom.userData.islandIds;
                const indexAttr = geom.index;
                const faceIdx = intersect.faceIndex;
                
                if (indexAttr && faceIdx !== undefined) {
                    const idx0 = indexAttr.getX(faceIdx * 3);
                    const islandId = islandIds[idx0];
                    const meshName = mesh.name || "Piece";

                    if (!hoveredItem || hoveredItem.meshName !== meshName || hoveredItem.islandId !== islandId) {
                        hoveredItem = {
                            type: 'island',
                            meshName: meshName,
                            islandId: islandId
                        };
                        update3DHighlight();
                        syncListHoverState(meshName, islandId);
                    }
                    return;
                }
            }
        }

        if (hoveredItem) {
            hoveredItem = null;
            update3DHighlight();
            syncListHoverState(null, null);
        }
    });

    renderer.domElement.addEventListener('click', (e) => {
        const uvDrawer = document.getElementById('uv-editor-drawer');
        if (!uvDrawer || !uvDrawer.classList.contains('open') || !simplifiedGroup) return;

        const rect = renderer.domElement.getBoundingClientRect();
        mouse3D.x = ((e.clientX - rect.left) / rect.width) * 2 - 1;
        mouse3D.y = -((e.clientY - rect.top) / rect.height) * 2 + 1;

        raycaster.setFromCamera(mouse3D, camera);
        const intersects = raycaster.intersectObjects(simplifiedGroup.children, true);

        if (intersects.length > 0) {
            const intersect = intersects[0];
            const mesh = intersect.object;
            const geom = mesh.geometry;
            
            if (geom && geom.userData && geom.userData.islandIds) {
                const islandIds = geom.userData.islandIds;
                const indexAttr = geom.index;
                const faceIdx = intersect.faceIndex;
                
                if (indexAttr && faceIdx !== undefined) {
                    const idx0 = indexAttr.getX(faceIdx * 3);
                    const islandId = islandIds[idx0];
                    const meshName = mesh.name || "Piece";

                    selectedItem = {
                        type: 'island',
                        meshName: meshName,
                        islandId: islandId
                    };
                    
                    rebuildHierarchyUI();
                    
                    const key = `island:${meshName}:${islandId}`;
                    let transform = itemTransforms.get(key);
                    if (!transform) {
                        transform = { scaleU: 1.0, scaleV: 1.0, offsetU: 0.0, offsetV: 0.0, rotation: 0.0, visible: true, flipV: false };
                        itemTransforms.set(key, transform);
                    }
                    
                    const sliderSU = document.getElementById('editor-scale-u');
                    const sliderSV = document.getElementById('editor-scale-v');
                    const sliderOU = document.getElementById('editor-offset-u');
                    const sliderOV = document.getElementById('editor-offset-v');
                    const sliderRot = document.getElementById('editor-rotation');
                    
                    if (sliderSU) {
                        sliderSU.value = transform.scaleU * 100;
                        sliderSV.value = transform.scaleV * 100;
                        sliderOU.value = transform.offsetU * 100;
                        sliderOV.value = transform.offsetV * 100;
                        sliderRot.value = transform.rotation;
                        
                        document.getElementById('val-scale-u').innerText = `${transform.scaleU.toFixed(1)}x`;
                        document.getElementById('val-scale-v').innerText = `${transform.scaleV.toFixed(1)}x`;
                        document.getElementById('val-offset-u').innerText = `${transform.offsetU.toFixed(2)}`;
                        document.getElementById('val-offset-v').innerText = `${transform.offsetV.toFixed(2)}`;
                        document.getElementById('val-rotation').innerText = `${transform.rotation.toFixed(0)}°`;
                    }
                    
                    drawUVWireframe();
                }
            }
        }
    });
}

// --- Drag & Drop Multi-File Loader ---
function handleMultipleFiles(fileList) {
    if (fileList.length === 0) return;

    let objFile = null;
    const textureFiles = [];

    for (let i = 0; i < fileList.length; i++) {
        const file = fileList[i];
        const ext = file.name.toLowerCase().split('.').pop();
        if (ext === 'obj') {
            objFile = file;
        } else if (['png', 'jpg', 'jpeg'].includes(ext)) {
            textureFiles.push(file);
        }
    }

    if (!objFile) {
        alert('Missing model file. Please select or drag in at least one Autodesk .obj file.');
        return;
    }

    originalFileName = objFile.name;
    
    // Calculate total size of all files combined
    let totalSize = objFile.size;
    textureFiles.forEach(f => totalSize += f.size);
    const sizeInMB = (totalSize / (1024 * 1024)).toFixed(2);
    document.getElementById('file-size-badge').innerText = `${sizeInMB} MB`;
    document.getElementById('loaded-file-name').innerText = objFile.name;

    showLoader("Loading Assets", `Reading ${objFile.name} and resolving ${textureFiles.length} texture maps...`);

    const objReader = new FileReader();
    objReader.onerror = () => {
        hideLoader();
        alert('Error occurred reading the .obj file.');
    };

    objReader.onload = (event) => {
        const objText = event.target.result;
        
        if (textureFiles.length > 0) {
            showLoader("Loading Textures", `Parsing ${textureFiles.length} image files...`);
            loadTexturesParallel(textureFiles).then(() => {
                // Textures detected: automatically uncheck Lock Borders!
                // Locking borders on textured meshes causes UV seams to lock up the decimation.
                const lockBordersChk = document.getElementById('lock-borders-chk');
                if (lockBordersChk && lockBordersChk.checked) {
                    console.log("Textures detected: Automatically disabling Lock Mesh Borders to allow decimation across UV seams.");
                    lockBordersChk.checked = false;
                    options.lockBorders = false;
                }
                
                parseAndLoadOBJ(objText);
            }).catch(err => {
                console.error("Failed to load some textures:", err);
                parseAndLoadOBJ(objText); // continue loading OBJ even if textures fail
            });
        } else {
            // No textures, clean up previous textures
            cleanupTextures();
            parseAndLoadOBJ(objText);
        }
    };

    objReader.readAsText(objFile);
}

// Load and classify textures in parallel
function loadTexturesParallel(files) {
    cleanupTextures();
    const loaderPromises = files.map(file => {
        return new Promise((resolve) => {
            const name = file.name.toLowerCase();
            const objectURL = URL.createObjectURL(file);
            textureObjectURLs.push(objectURL);

            const textureLoader = new THREE.TextureLoader();
            textureLoader.load(
                objectURL,
                (texture) => {
                    // Auto-classify texture based on keywords in name
                    let type = 'color';
                    let label = 'Base Color';
                    let badgeClass = 'color';

                    if (name.includes('normal') || name.includes('norm')) {
                        type = 'normal';
                        label = 'Normal Map';
                        badgeClass = 'normal';
                    } else if (name.includes('rough') || name.includes('roughness')) {
                        type = 'roughness';
                        label = 'Roughness';
                        badgeClass = 'roughness';
                    } else if (name.includes('metal') || name.includes('metallic') || name.includes('metalness')) {
                        type = 'roughness'; // use roughness map slot for metallics/gloss
                        label = 'Metallic';
                        badgeClass = 'roughness';
                    } else if (name.includes('ao') || name.includes('occlusion') || name.includes('ambient')) {
                        type = 'ao';
                        label = 'AO Map';
                        badgeClass = 'ao';
                    }

                    // Configure texture parameters
                    texture.wrapS = THREE.RepeatWrapping;
                    texture.wrapT = THREE.RepeatWrapping;
                    texture.colorSpace = (type === 'color') ? THREE.SRGBColorSpace : THREE.NoColorSpace;

                    // Add badge to UI
                    const badge = document.createElement('span');
                    badge.className = `texture-badge ${badgeClass}`;
                    badge.innerText = `✓ ${label}`;
                    badge.title = file.name;
                    document.getElementById('loaded-textures-list').appendChild(badge);

                    console.log(`Classified texture map: "${file.name}" -> ${label}`);
                    resolve({ type, texture });
                },
                undefined,
                (err) => {
                    console.error(`Failed to load texture ${file.name}:`, err);
                    resolve(null); // Resolve null so Promise.all doesn't fail completely
                }
            );
        });
    });

    return Promise.all(loaderPromises).then((results) => {
        let textureLoaded = false;
        results.forEach(result => {
            if (result) {
                loadedTextures[result.type] = result.texture;
                textureLoaded = true;
            }
        });

        if (textureLoaded) {
            // Unlock Textured Material option in UI
            const texturedRadio = document.getElementById('mat-textured');
            const texturedLabel = document.getElementById('lbl-textured');
            texturedLabel.classList.remove('disabled-label');
            texturedLabel.removeAttribute('title');
            
            // Automatically switch material finish to Textured
            texturedRadio.checked = true;
            options.materialStyle = 'textured';
        }
    });
}

// Clear textures from GPU memory
function cleanupTextures() {
    Object.keys(loadedTextures).forEach(key => {
        if (loadedTextures[key]) {
            loadedTextures[key].dispose();
            loadedTextures[key] = null;
        }
    });
    
    // Revoke object URLs to free browser memory
    textureObjectURLs.forEach(url => URL.revokeObjectURL(url));
    textureObjectURLs = [];

    // Reset UI Badges
    document.getElementById('loaded-textures-list').innerHTML = "";

    // Lock Textured Material option
    const texturedRadio = document.getElementById('mat-textured');
    const texturedLabel = document.getElementById('lbl-textured');
    if (texturedRadio) {
        texturedRadio.checked = false;
        texturedLabel.classList.add('disabled-label');
        texturedLabel.title = "Drag in textures (.png, .jpg) to unlock";
    }
}

// --- OBJ Parser & Viewport Normalization ---
function parseAndLoadOBJ(text) {
    showLoader("Parsing Mesh", "Building 3D geometries...");
    
    // Defer execution slightly to let UI thread render the loader
    setTimeout(() => {
        try {
            console.log("--- parseAndLoadOBJ() Started ---");
            const loader = new OBJLoader();
            console.log("Parsing OBJ text content...");
            const group = loader.parse(text);
            console.log("OBJ parsed successfully. Group children count:", group.children.length);
            
            if (!group || group.children.length === 0) {
                throw new Error("No meshes found in the OBJ file.");
            }

            // Clean previous model
            cleanupModel();

            // Center and Normalize the model to a unit bounding box
            console.log("Normalizing model transform (centering and scaling to fit viewport)...");
            normalizeModelTransform(group);
            console.log(`Model normalized: scale factor = ${normalizationScale.toFixed(6)}, offset = [${normalizationOffset.x.toFixed(3)}, ${normalizationOffset.y.toFixed(3)}, ${normalizationOffset.z.toFixed(3)}]`);

            originalGroup = group;
            scene.add(originalGroup);

            // Hide original model from view (we will render the simplified one instead)
            originalGroup.visible = false;

            // Calculate original statistics
            const stats = getGroupStats(originalGroup);
            console.log("Original model stats calculated: faces =", stats.faces, "vertices =", stats.vertices);
            document.getElementById('stat-orig-faces').innerText = stats.faces.toLocaleString();
            document.getElementById('stat-orig-verts').innerText = stats.vertices.toLocaleString();

            // Transition UI
            document.getElementById('upload-card').classList.add('hidden');
            document.getElementById('stats-card').classList.remove('hidden');
            document.getElementById('controls-card').classList.remove('hidden');
            document.getElementById('actions-panel').classList.remove('hidden');

            // Reset Ratio slider
            const ratioSlider = document.getElementById('ratio-slider');
            ratioSlider.value = 50;
            document.getElementById('ratio-value').innerText = "50%";
            options.ratio = 0.5;

            // Perform initial decimation
            console.log("Triggering initial 50% simplification...");
            triggerSimplification();
            console.log("Fitting camera to model viewport...");
            fitCameraToModel();
            
            // Show UV tool panel
            document.getElementById('uv-tool').classList.remove('hidden');
            
            console.log("Model loading and initial simplification finished successfully.");

        } catch (error) {
            console.error(error);
            alert(`Failed to load 3D model: ${error.message}`);
            hideLoader();
        }
    }, 50);
}

// Center geometry and scale group to a comfortable size for view
function normalizeModelTransform(group) {
    // Force compute bounding boxes for all geometries
    group.traverse((child) => {
        if (child.isMesh && child.geometry) {
            child.geometry.computeBoundingBox();
            child.geometry.computeBoundingSphere();
        }
    });

    const box = new THREE.Box3().setFromObject(group);
    const size = new THREE.Vector3();
    box.getSize(size);
    const center = new THREE.Vector3();
    box.getCenter(center);

    // Find maximum dimension to scale uniformly
    const maxDim = Math.max(size.x, size.y, size.z);
    
    // Scale model so its bounding box fits inside a box of 10x10x10
    const targetDim = 9.0;
    normalizationScale = maxDim > 0 ? targetDim / maxDim : 1.0;
    normalizationOffset.copy(center).multiplyScalar(-1); // Shift to origin

    // Apply normalization transformations
    group.position.copy(normalizationOffset).multiplyScalar(normalizationScale);
    group.scale.setScalar(normalizationScale);

    // Adjust grid helper to match model's height floor
    // Place grid right under the model's bounding box base
    const minY = (box.min.y + normalizationOffset.y) * normalizationScale;
    gridHelper.position.y = minY - 0.01; // subtle offset to avoid z-fighting
    axesHelper.position.y = minY + 0.01;
}

// Get aggregate face/vertex counts of a Group
function getGroupStats(group) {
    let vertices = 0;
    let faces = 0;

    group.traverse((child) => {
        if (child.isMesh && child.geometry) {
            const geom = child.geometry;
            const position = geom.attributes.position;
            if (position) {
                vertices += position.count;
            }
            if (geom.index) {
                faces += geom.index.count / 3;
            } else if (position) {
                faces += position.count / 3;
            }
        }
    });

    return { vertices, faces };
}

// Clean up models from memory
function cleanupModel() {
    if (originalGroup) {
        scene.remove(originalGroup);
        disposeGroup(originalGroup);
        originalGroup = null;
    }
    if (simplifiedGroup) {
        scene.remove(simplifiedGroup);
        disposeGroup(simplifiedGroup);
        simplifiedGroup = null;
    }
    if (wireframeOverlay) {
        scene.remove(wireframeOverlay);
        disposeGroup(wireframeOverlay);
        wireframeOverlay = null;
    }
}

function disposeGroup(group) {
    group.traverse((child) => {
        if (child.isMesh) {
            if (child.geometry) child.geometry.dispose();
            if (child.material) {
                if (Array.isArray(child.material)) {
                    child.material.forEach(m => m.dispose());
                } else {
                    child.material.dispose();
                }
            }
        } else if (child.isLineSegments) {
            if (child.geometry) child.geometry.dispose();
            if (child.material) child.material.dispose();
        }
    });
}

// --- Decimation / Meshopt Simplification Engine ---
function triggerSimplification() {
    if (!originalGroup || !isWasmReady) {
        console.warn("triggerSimplification aborted: originalGroup loaded =", !!originalGroup, "isWasmReady =", isWasmReady);
        return;
    }

    console.log(`\n--- triggerSimplification() Starting decimation ---`);
    console.log(`Target ratio = ${options.ratio} (${Math.round(options.ratio * 100)}%), targetError = ${options.targetError}, lockBorders = ${options.lockBorders}, regularize = ${options.regularize}`);
    const startTime = performance.now();

    // Reset Hierarchy cache for this rebuild
    piecesHierarchy = [];

    // 1. Remove previous simplified model & wireframe
    if (simplifiedGroup) {
        scene.remove(simplifiedGroup);
        disposeGroup(simplifiedGroup);
    }
    if (wireframeOverlay) {
        scene.remove(wireframeOverlay);
        disposeGroup(wireframeOverlay);
    }

    // 2. Clone original group to perform decimation on geometries
    simplifiedGroup = originalGroup.clone();
    simplifiedGroup.name = "simplified_model";
    simplifiedGroup.visible = true;

    let simplifiedStats = { vertices: 0, faces: 0 };
    let meshIndex = 0;

    // 3. Traverse and decimate individual meshes
    simplifiedGroup.traverse((child) => {
        if (child.isMesh) {
            meshIndex++;
            const originalGeom = child.geometry;
            if (!originalGeom || !originalGeom.attributes.position) {
                console.warn(`Sub-mesh #${meshIndex} (${child.name || "unnamed"}) has no positions attribute. Skipping.`);
                return;
            }

            const originalVertCount = originalGeom.attributes.position.count;
            const originalFaceCount = originalGeom.index ? originalGeom.index.count / 3 : originalVertCount / 3;
            console.log(`Sub-mesh #${meshIndex} (${child.name || "unnamed"}): Original Verts = ${originalVertCount}, Original Faces = ${originalFaceCount}, Indexed = ${!!originalGeom.index}`);

            // Detect UV Islands on the original geometry topologically
            console.log(`Detecting UV Islands topology for sub-mesh...`);
            const islands = detectUVIslands(originalGeom);
            console.log(`Detected ${islands.length} UV Islands.`);
            
            // Cache in pieces list
            const meshName = child.name || `Piece #${meshIndex}`;
            piecesHierarchy.push({
                meshName: meshName,
                meshRef: child,
                islands: islands
            });

            // Weld vertices strictly by position while retaining representative UV coordinates.
            console.log(`Welding vertices strictly by position while preserving UV mapping...`);
            const weldedGeom = weldGeometryByUVIslands(originalGeom, islands);
            
            // Cache active welded geometry for UV projection and re-mapping transformations
            activeWeldedGeom = weldedGeom;

            const positionAttr = weldedGeom.attributes.position;
            const indexAttr = weldedGeom.index;

            const positions = positionAttr.array; // Float32Array
            const indices = indexAttr.array;       // Uint32Array / Uint16Array

            const weldedVertCount = positionAttr.count;
            const weldedIndexCount = indices.length;
            console.log(`Post-weld: Verts = ${weldedVertCount}, Indices = ${weldedIndexCount} (Faces = ${weldedIndexCount / 3})`);
            
            // Calculate target index count based on ratio (must be multiple of 3)
            const targetIndexCount = Math.max(0, Math.floor((weldedIndexCount * options.ratio) / 3) * 3);
            console.log(`Target index count calculated: ${targetIndexCount} (Target Faces = ${targetIndexCount / 3})`);

            if (targetIndexCount === 0 || targetIndexCount >= weldedIndexCount) {
                console.log(`Target index count is 0 or exceeds welded count. Keeping welded geometry as-is.`);
                child.geometry = weldedGeom;
                simplifiedStats.vertices += weldedVertCount;
                simplifiedStats.faces += weldedIndexCount / 3;
                return;
            }

            // Setup Meshopt constraints flags
            const flags = [];
            if (options.lockBorders) flags.push('LockBorder');
            if (options.regularize) flags.push('Regularize');

            // Run WASM Edge-Collapse Simplification
            let simplifiedIndices, error;
            try {
                const uvAttr = weldedGeom.attributes.uv;
                if (uvAttr) {
                    console.log("Invoking MeshoptSimplifier.simplifyWithAttributes (UV-aware)...");
                    const uvs = uvAttr.array;
                    const uvStride = 2;
                    const weights = [1.0, 1.0]; // Weight of U and V coordinate errors
                    
                    const result = MeshoptSimplifier.simplifyWithAttributes(
                        indices,
                        positions,
                        3, // stride in floats (x,y,z)
                        uvs,
                        uvStride,
                        weights,
                        null, // vertex_lock
                        targetIndexCount,
                        options.targetError,
                        flags
                    );
                    simplifiedIndices = result[0];
                    error = result[1];
                } else {
                    console.log("Invoking MeshoptSimplifier.simplify (positions-only)...");
                    const result = MeshoptSimplifier.simplify(
                        indices,
                        positions,
                        3, // stride in floats (x,y,z)
                        targetIndexCount,
                        options.targetError,
                        flags
                    );
                    simplifiedIndices = result[0];
                    error = result[1];
                }
                console.log(`MeshoptSimplifier success. Output indices length = ${simplifiedIndices.length} (Faces = ${simplifiedIndices.length / 3}), Returned error = ${error}`);
            } catch (err) {
                console.error("MeshoptSimplifier.simplify crashed with error:", err);
                // Rollback to welded
                child.geometry = weldedGeom;
                simplifiedStats.vertices += weldedVertCount;
                simplifiedStats.faces += weldedIndexCount / 3;
                return;
            }

            // Reconstruct Geometry
            const simplifiedGeom = weldedGeom.clone();
            
            // Index Filtering Logic to hide Pieces or Islands dynamically
            let visibleIndices = simplifiedIndices;
            const pieceKey = `piece:${meshName}`;
            const pieceTransform = itemTransforms.get(pieceKey);
            const isPieceVisible = pieceTransform ? pieceTransform.visible : true;

            if (!isPieceVisible) {
                // Completely hide piece
                visibleIndices = new Uint32Array(0);
            } else {
                // Filter out indices of hidden islands
                const islandIds = weldedGeom.userData.islandIds;
                const filtered = [];
                for (let i = 0; i < simplifiedIndices.length; i += 3) {
                    const idx0 = simplifiedIndices[i];
                    const idx1 = simplifiedIndices[i + 1];
                    const idx2 = simplifiedIndices[i + 2];
                    
                    const islandId = islandIds[idx0];
                    const islandKey = `island:${meshName}:${islandId}`;
                    const islandTransform = itemTransforms.get(islandKey);
                    const isIslandVisible = islandTransform ? islandTransform.visible : true;
                    
                    if (isIslandVisible) {
                        filtered.push(idx0, idx1, idx2);
                    }
                }
                visibleIndices = new Uint32Array(filtered);
            }

            simplifiedGeom.setIndex(new THREE.BufferAttribute(visibleIndices, 1));
            
            // Apply procedural UV projection and individual transforms
            applyUVProjectionToGeometry(simplifiedGeom, weldedGeom, meshName);
            
            // Recompute normals to match new decimated shape contours
            simplifiedGeom.computeVertexNormals();

            // Update Mesh geometry
            child.geometry = simplifiedGeom;

            // Add to statistics
            simplifiedStats.vertices += weldedVertCount; 
            simplifiedStats.faces += simplifiedIndices.length / 3;
        }
    });

    // 4. Set material styles and shading
    updateMaterialStyle();
    updateShadingMode();

    // 5. Build wireframe overlay if enabled
    buildWireframeOverlay();

    // 6. Add simplified model back to scene
    scene.add(simplifiedGroup);

    // Update Performance UI
    const endTime = performance.now();
    lastSimplificationTime = endTime - startTime;

    // Update Stats Card
    document.getElementById('stat-simp-faces').innerText = simplifiedStats.faces.toLocaleString();
    document.getElementById('stat-simp-verts').innerText = simplifiedStats.vertices.toLocaleString();
    
    const redPct = Math.round((1 - options.ratio) * 100);
    document.getElementById('reduction-percent').innerText = `${redPct}%`;
    document.getElementById('reduction-progress').style.width = `${redPct}%`;

    // Update HUD
    document.getElementById('hud-time').innerText = `${lastSimplificationTime.toFixed(0)} ms`;
    
    // Rebuild tree Hierarchy UI list
    rebuildHierarchyUI();

    // Redraw 2D UV layout canvas
    drawUVWireframe();

    hideLoader();
}

// --- Wireframe Construction ---
function buildWireframeOverlay() {
    if (!simplifiedGroup) return;

    // Remove old overlay first
    if (wireframeOverlay) {
        scene.remove(wireframeOverlay);
        disposeGroup(wireframeOverlay);
        wireframeOverlay = null;
    }

    // Return if overlay is not enabled
    if (options.viewMode === 'solid') return;

    wireframeOverlay = new THREE.Group();
    wireframeOverlay.name = "wireframe_overlay";
    wireframeOverlay.position.copy(simplifiedGroup.position);
    wireframeOverlay.scale.copy(simplifiedGroup.scale);
    wireframeOverlay.rotation.copy(simplifiedGroup.rotation);

    simplifiedGroup.traverse((child) => {
        if (child.isMesh) {
            const wireframeGeom = new THREE.WireframeGeometry(child.geometry);
            const lines = new THREE.LineSegments(wireframeGeom);
            
            // Premium Cyan/Neon wireframe styling
            lines.material = new THREE.LineBasicMaterial({
                color: 0x00d2ff,
                transparent: true,
                opacity: options.viewMode === 'wire' ? 0.8 : 0.38,
                depthWrite: false, // Prevents ugly z-fighting flickering
            });

            // Match sub-mesh transformation offsets
            lines.position.copy(child.position);
            lines.rotation.copy(child.rotation);
            lines.scale.copy(child.scale);

            wireframeOverlay.add(lines);
        }
    });

    scene.add(wireframeOverlay);
}

// --- Apply Material style ---
function updateMaterialStyle() {
    if (!simplifiedGroup) return;

    const currentMaterial = materials[options.materialStyle];

    // If style is textured, bind our loaded maps to the material
    if (options.materialStyle === 'textured') {
        materials.textured.map = loadedTextures.color || null;
        materials.textured.normalMap = loadedTextures.normal || null;
        materials.textured.roughnessMap = loadedTextures.roughness || null;
        materials.textured.metalnessMap = loadedTextures.roughness || null; // reuse roughness map or separate
        materials.textured.aoMap = loadedTextures.ao || null;
        materials.textured.needsUpdate = true;
    }

    simplifiedGroup.traverse((child) => {
        if (child.isMesh) {
            child.material = currentMaterial;
            child.castShadow = (options.materialStyle !== 'xray');
            child.receiveShadow = (options.materialStyle !== 'xray');
        }
    });

    // Update display modes in case wireframe transparency rules change
    updateDisplayMode();
}

// --- Apply Shading Mode (Flat vs Smooth) ---
function updateShadingMode() {
    if (!simplifiedGroup) return;

    simplifiedGroup.traverse((child) => {
        if (child.isMesh) {
            if (options.shadingMode === 'flat') {
                child.material.flatShading = true;
            } else {
                child.material.flatShading = false;
            }
            child.material.needsUpdate = true;
        }
    });
}

// --- Apply Display Mode (Solid vs Wireframe Overlay) ---
function updateDisplayMode() {
    if (!simplifiedGroup) return;

    // Toggle solid visibility
    simplifiedGroup.traverse((child) => {
        if (child.isMesh) {
            if (options.viewMode === 'wire') {
                child.visible = false;
            } else {
                child.visible = true;
                // If it is Holo / X-Ray, adjust transparency
                if (options.materialStyle === 'xray') {
                    child.material.opacity = (options.viewMode === 'both') ? 0.15 : 0.32;
                }
            }
        }
    });

    // Rebuild wireframe overlay
    buildWireframeOverlay();
}

// --- Camera Navigation Presets ---
function fitCameraToModel() {
    if (!simplifiedGroup) return;

    const box = new THREE.Box3().setFromObject(simplifiedGroup);
    const sphere = new THREE.Sphere();
    box.getBoundingSphere(sphere);

    const radius = sphere.radius;
    const center = sphere.center;

    // Calculate camera distance to frame the sphere nicely
    const fov = camera.fov * (Math.PI / 180);
    let cameraDist = Math.abs(radius / Math.sin(fov / 2));
    
    // Add safety margin
    cameraDist *= 1.25;

    camera.position.set(center.x + cameraDist * 0.7, center.y + cameraDist * 0.5, center.z + cameraDist * 0.7);
    controls.target.copy(center);
    controls.update();
}

function setCameraPreset(view) {
    if (!simplifiedGroup) return;

    const box = new THREE.Box3().setFromObject(simplifiedGroup);
    const center = new THREE.Vector3();
    box.getCenter(center);
    const size = new THREE.Vector3();
    box.getSize(size);
    const distance = Math.max(size.x, size.y, size.z) * 1.5;

    switch (view) {
        case 'top':
            camera.position.set(center.x, center.y + distance, center.z);
            break;
        case 'front':
            camera.position.set(center.x, center.y, center.z + distance);
            break;
        case 'side':
            camera.position.set(center.x + distance, center.y, center.z);
            break;
    }
    controls.target.copy(center);
    controls.update();
}

// --- Export OBJ File ---
function exportModel() {
    if (!simplifiedGroup) return;

    showLoader("Exporting OBJ", "Re-packaging simplified mesh files...");

    setTimeout(() => {
        try {
            const exporter = new OBJExporter();

            // 1. Clone the simplified model to revert the normalization transforms
            // We want to export the mesh in its original coordinate system, scale, and offset!
            const exportClone = simplifiedGroup.clone();
            exportClone.name = originalGroup.name;

            // Revert Bounding Box Normalization
            // Original transform: (vertex + offset) * scale
            // Reverted transform: vertex / scale - offset
            exportClone.position.set(0, 0, 0);
            exportClone.scale.setScalar(1.0);
            
            exportClone.traverse((child) => {
                if (child.isMesh) {
                    // Apply inverse normalization directly to vertices so that it preserves
                    // the original spatial positions exactly as in the imported file.
                    child.geometry = child.geometry.clone();
                    
                    const positions = child.geometry.attributes.position;
                    for (let i = 0; i < positions.count; i++) {
                        let x = positions.getX(i);
                        let y = positions.getY(i);
                        let z = positions.getZ(i);

                        // Invert the: (val + offset) * scale
                        x = (x / normalizationScale) - normalizationOffset.x;
                        y = (y / normalizationScale) - normalizationOffset.y;
                        z = (z / normalizationScale) - normalizationOffset.z;

                        positions.setXYZ(i, x, y, z);
                    }
                    positions.needsUpdate = true;
                    child.geometry.computeVertexNormals();
                    child.geometry.computeBoundingBox();
                    child.geometry.computeBoundingSphere();
                }
            });

            // 2. Parse clone to OBJ string
            const resultString = exporter.parse(exportClone);
            
            // 3. Trigger Browser Download
            const blob = new Blob([resultString], { type: 'text/plain' });
            const link = document.createElement('a');
            link.href = URL.createObjectURL(blob);
            
            // Format filename: original_name_simplified_50pct.obj
            const baseName = originalFileName.substring(0, originalFileName.lastIndexOf('.'));
            const suffix = `_simplified_${Math.round(options.ratio * 100)}pct.obj`;
            link.download = baseName + suffix;
            
            link.click();
            
            // Cleanup
            URL.revokeObjectURL(link.href);
            disposeGroup(exportClone);

            hideLoader();
        } catch (error) {
            console.error(error);
            alert(`Failed to export OBJ model: ${error.message}`);
            hideLoader();
        }
    }, 50);
}

// --- Reset App to Uploader State ---
function resetUploader() {
    cleanupModel();
    cleanupTextures();
    
    // Hide and reset UV tool panel
    document.getElementById('uv-tool').classList.add('hidden');
    document.getElementById('uv-mode-select').value = 'original';
    uvOptions.mode = 'original';
    document.getElementById('uv-scale-slider').value = 100;
    document.getElementById('uv-scale-val').innerText = '1.0x';
    uvOptions.scale = 1.0;

    // Clear selection and hierarchy states
    selectedItem = null;
    update3DHighlight();
    itemTransforms.clear();
    piecesHierarchy = [];
    activeWeldedGeom = null;
    
    // Clear Tree UI
    const tree = document.getElementById('hierarchy-tree');
    if (tree) tree.innerHTML = "";

    // Slide close and reset UV layout editor drawer
    const uvDrawer = document.getElementById('uv-editor-drawer');
    if (uvDrawer) {
        uvDrawer.classList.remove('open');
    }
    
    const sliderSU = document.getElementById('editor-scale-u');
    const sliderSV = document.getElementById('editor-scale-v');
    const sliderOU = document.getElementById('editor-offset-u');
    const sliderOV = document.getElementById('editor-offset-v');
    const sliderRot = document.getElementById('editor-rotation');
    
    if (sliderSU) {
        sliderSU.value = 100;
        sliderSV.value = 100;
        sliderOU.value = 0;
        sliderOV.value = 0;
        sliderRot.value = 0;
        editorUVTransforms.scaleU = 1.0;
        editorUVTransforms.scaleV = 1.0;
        editorUVTransforms.offsetU = 0.0;
        editorUVTransforms.offsetV = 0.0;
        editorUVTransforms.rotation = 0.0;
        editorUVTransforms.flipV = false;
        
        document.getElementById('val-scale-u').innerText = '1.0x';
        document.getElementById('val-scale-v').innerText = '1.0x';
        document.getElementById('val-offset-u').innerText = '0.00';
        document.getElementById('val-offset-v').innerText = '0.00';
        document.getElementById('val-rotation').innerText = '0°';
    }
    
    activeWeldedGeom = null;
    
    // Show Upload Card, Hide others
    document.getElementById('upload-card').classList.remove('hidden');
    document.getElementById('stats-card').classList.add('hidden');
    document.getElementById('controls-card').classList.add('hidden');
    document.getElementById('actions-panel').classList.add('hidden');

    // Reset grid height
    gridHelper.position.y = 0;
    axesHelper.position.y = 0.01;
    
    // Reset File input
    document.getElementById('file-input').value = "";
    
    // Reset Camera
    camera.position.set(10, 8, 12);
    controls.target.set(0, 0, 0);
    controls.update();
}

// --- Loader Spinner Helpers ---
function showLoader(title, description) {
    document.getElementById('loader-title').innerText = title;
    document.getElementById('loader-desc').innerText = description;
    document.getElementById('loader').classList.remove('hidden');
}

function hideLoader() {
    document.getElementById('loader').classList.add('hidden');
}

// Custom topological welder that merges vertices strictly by 3D coordinates
// but preserves a representative UV coordinate for each unique vertex.
// This allows full decimation of textured meshes without losing mapping coordinates.
function weldGeometryByPosition(geometry) {
    const positionAttr = geometry.attributes.position;
    const uvAttr = geometry.attributes.uv;
    const hasUV = !!uvAttr;

    const uniquePositions = [];
    const uniqueUVs = [];
    const positionMap = new Map();
    const indexMapping = new Int32Array(positionAttr.count);

    let uniqueCount = 0;

    for (let i = 0; i < positionAttr.count; i++) {
        const x = positionAttr.getX(i);
        const y = positionAttr.getY(i);
        const z = positionAttr.getZ(i);
        
        // High-precision coordinate key
        const key = `${x.toFixed(6)},${y.toFixed(6)},${z.toFixed(6)}`;
        
        if (positionMap.has(key)) {
            indexMapping[i] = positionMap.get(key);
        } else {
            positionMap.set(key, uniqueCount);
            indexMapping[i] = uniqueCount;
            
            uniquePositions.push(x, y, z);
            if (hasUV) {
                uniqueUVs.push(uvAttr.getX(i), uvAttr.getY(i));
            }
            
            uniqueCount++;
        }
    }

    // Reconstruct index array
    let indices;
    if (geometry.index) {
        const originalIndices = geometry.index.array;
        indices = new Uint32Array(originalIndices.length);
        for (let i = 0; i < originalIndices.length; i++) {
            indices[i] = indexMapping[originalIndices[i]];
        }
    } else {
        // Non-indexed, generate indices from vertex mapping
        indices = new Uint32Array(positionAttr.count);
        for (let i = 0; i < positionAttr.count; i++) {
            indices[i] = indexMapping[i];
        }
    }

    // Create new welded geometry
    const weldedGeom = new THREE.BufferGeometry();
    weldedGeom.setAttribute('position', new THREE.Float32BufferAttribute(uniquePositions, 3));
    if (hasUV) {
        weldedGeom.setAttribute('uv', new THREE.Float32BufferAttribute(uniqueUVs, 2));
    }
    weldedGeom.setIndex(new THREE.BufferAttribute(indices, 1));
    
    return weldedGeom;
}


// Apply UV Projection and editor transforms to all meshes in a Group
function applyUVProjectionToGroup(group) {
    if (!group) return;
    
    group.traverse((child) => {
        if (child.isMesh && child.geometry) {
            applyUVProjectionToGeometry(child.geometry, activeWeldedGeom, child.name || "Piece");
        }
    });
}

// Apply procedural UV projection and editor interactive transforms in WebGL space
function applyUVProjectionToGeometry(geometry, baseGeom, meshName) {
    const positionAttr = geometry.attributes.position;
    if (!positionAttr) return;

    const count = positionAttr.count;
    const uvs = new Float32Array(count * 2);

    // Get base UVs first if available in baseGeom
    const baseUVAttr = baseGeom ? baseGeom.attributes.uv : null;
    const hasBaseUV = !!baseUVAttr;

    // Get the welded vertex-to-island mapping ID
    const islandIds = baseGeom ? baseGeom.userData.islandIds : null;

    // Bounding box for projections
    let box, size, center;
    if (uvOptions.mode !== 'original') {
        geometry.computeBoundingBox();
        box = geometry.boundingBox;
        size = new THREE.Vector3();
        box.getSize(size);
        center = new THREE.Vector3();
        box.getCenter(center);
    }

    // Get Piece global transform
    const pieceKey = `piece:${meshName}`;
    let pTrans = itemTransforms.get(pieceKey);
    if (!pTrans) {
        pTrans = { scaleU: 1.0, scaleV: 1.0, offsetU: 0.0, offsetV: 0.0, rotation: 0.0, visible: true, flipV: false };
        itemTransforms.set(pieceKey, pTrans);
    }

    const cx = 0.5;
    const cy = 0.5;

    for (let i = 0; i < count; i++) {
        let u = 0.5;
        let v = 0.5;

        if (uvOptions.mode === 'original') {
            if (hasBaseUV) {
                u = baseUVAttr.getX(i);
                v = baseUVAttr.getY(i);
            }
        } else {
            const vx = positionAttr.getX(i);
            const vy = positionAttr.getY(i);
            const vz = positionAttr.getZ(i);

            switch (uvOptions.mode) {
                case 'planar-front':
                    u = size.x > 0 ? (vx - box.min.x) / size.x : 0.5;
                    v = size.y > 0 ? (vy - box.min.y) / size.y : 0.5;
                    break;
                case 'planar-top':
                    u = size.x > 0 ? (vx - box.min.x) / size.x : 0.5;
                    v = size.z > 0 ? (vz - box.min.z) / size.z : 0.5;
                    break;
                case 'spherical': {
                    const dx = vx - center.x;
                    const dy = vy - center.y;
                    const dz = vz - center.z;
                    const r = Math.sqrt(dx*dx + dy*dy + dz*dz);
                    u = 0.5 + Math.atan2(dz, dx) / (2 * Math.PI);
                    v = 0.5 - Math.asin(r > 0 ? dy / r : 0) / Math.PI;
                    break;
                }
                case 'cylindrical': {
                    const dx = vx - center.x;
                    const dz = vz - center.z;
                    u = 0.5 + Math.atan2(dz, dx) / (2 * Math.PI);
                    v = size.y > 0 ? (vy - box.min.y) / size.y : 0.5;
                    break;
                }
            }
            // Apply the base projection scale
            u *= uvOptions.scale;
            v *= uvOptions.scale;
        }

        // Retrieve Island individual transform
        const islandId = islandIds ? islandIds[i] : 0;
        const islandKey = `island:${meshName}:${islandId}`;
        let iTrans = itemTransforms.get(islandKey);
        if (!iTrans) {
            iTrans = { scaleU: 1.0, scaleV: 1.0, offsetU: 0.0, offsetV: 0.0, rotation: 0.0, visible: true, flipV: false };
            itemTransforms.set(islandKey, iTrans);
        }

        // Combine Piece and Island transforms
        const combinedScaleU = pTrans.scaleU * iTrans.scaleU;
        const combinedScaleV = pTrans.scaleV * iTrans.scaleV;
        const combinedOffsetU = pTrans.offsetU + iTrans.offsetU;
        const combinedOffsetV = pTrans.offsetV + iTrans.offsetV;
        const combinedRot = (pTrans.rotation + iTrans.rotation) * Math.PI / 180;
        const shouldFlipV = pTrans.flipV ^ iTrans.flipV; // XOR flip

        // 1. Scale relative to (0.5, 0.5)
        u = (u - cx) * combinedScaleU + cx;
        v = (v - cy) * combinedScaleV + cy;

        // 2. Rotate relative to (0.5, 0.5)
        if (combinedRot !== 0) {
            const dx = u - cx;
            const dy = v - cy;
            u = cx + dx * Math.cos(combinedRot) - dy * Math.sin(combinedRot);
            v = cy + dx * Math.sin(combinedRot) + dy * Math.cos(combinedRot);
        }

        // 3. Offset Translate
        u += combinedOffsetU;
        v += combinedOffsetV;

        // 4. Flip V
        if (shouldFlipV) {
            v = 1 - v;
        }

        uvs[i * 2] = u;
        uvs[i * 2 + 1] = v;
    }

    // Set/overwrite uv attribute buffer
    geometry.setAttribute('uv', new THREE.BufferAttribute(uvs, 2));
    geometry.attributes.uv.needsUpdate = true;
}

// Draw the 2D UV wireframe overlay on top of the texture map
function drawUVWireframe() {
    const canvas = document.getElementById('uv-canvas');
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    
    // 1. Draw texture background (Base Color) or a default checkerboard pattern
    if (loadedTextures.color && loadedTextures.color.image) {
        ctx.drawImage(loadedTextures.color.image, 0, 0, canvas.width, canvas.height);
    } else {
        // Blender-style checkerboard
        const size = 16;
        for (let y = 0; y < canvas.height; y += size) {
            for (let x = 0; x < canvas.width; x += size) {
                ctx.fillStyle = ((x / size + y / size) % 2 === 0) ? '#1e2530' : '#121620';
                ctx.fillRect(x, y, size, size);
            }
        }
    }
    
    if (!simplifiedGroup) return;
    
    // 2. Draw 2D UV wireframe triangles
    simplifiedGroup.traverse((child) => {
        if (child.isMesh && child.geometry) {
            const geom = child.geometry;
            const uvAttr = geom.attributes.uv;
            const indexAttr = geom.index;
            
            if (!uvAttr) return;
            
            const meshName = child.name || "Piece";
            const islandIds = geom.userData.islandIds;
            
            // Check if Piece itself is visible
            const pieceKey = `piece:${meshName}`;
            const pieceTrans = itemTransforms.get(pieceKey);
            const isPieceVisible = pieceTrans ? pieceTrans.visible : true;
            if (!isPieceVisible) return; // do not draw if hidden
            
            const count = indexAttr ? indexAttr.count : uvAttr.count;
            
            for (let i = 0; i < count; i += 3) {
                const idx0 = indexAttr ? indexAttr.getX(i) : i;
                const idx1 = indexAttr ? indexAttr.getX(i + 1) : i + 1;
                const idx2 = indexAttr ? indexAttr.getX(i + 2) : i + 2;
                
                const u0 = uvAttr.getX(idx0);
                const v0 = uvAttr.getY(idx0);
                const u1 = uvAttr.getX(idx1);
                const v1 = uvAttr.getY(idx1);
                const u2 = uvAttr.getX(idx2);
                const v2 = uvAttr.getY(idx2);
                
                const islandId = islandIds ? islandIds[idx0] : 0;
                const islandKey = `island:${meshName}:${islandId}`;
                const islandTrans = itemTransforms.get(islandKey);
                const isIslandVisible = islandTrans ? islandTrans.visible : true;
                if (!isIslandVisible) continue; // do not draw if island is hidden
                
                // Determine highlight stroke color based on selection
                let strokeStyle = 'rgba(255, 255, 255, 0.2)';
                let lineWidth = 0.6;
                
                if (selectedItem) {
                    if (selectedItem.type === 'island' && selectedItem.meshName === meshName && selectedItem.islandId === islandId) {
                        // Highlight selected island in glowing cyan
                        strokeStyle = 'rgba(0, 210, 255, 1.0)';
                        lineWidth = 1.3;
                    } else if (selectedItem.type === 'piece' && selectedItem.meshName === meshName) {
                        // Highlight selected piece in soft cyan
                        strokeStyle = 'rgba(0, 210, 255, 0.6)';
                        lineWidth = 0.9;
                    }
                } else {
                    // Standard wireframe
                    strokeStyle = 'rgba(255, 255, 255, 0.45)';
                    lineWidth = 0.8;
                }
                
                ctx.strokeStyle = strokeStyle;
                ctx.lineWidth = lineWidth;
                
                // Map to 2D canvas coordinates (flipping Y because UV origin is bottom-left)
                const x0 = u0 * canvas.width;
                const y0 = (1 - v0) * canvas.height;
                const x1 = u1 * canvas.width;
                const y1 = (1 - v1) * canvas.height;
                const x2 = u2 * canvas.width;
                const y2 = (1 - v2) * canvas.height;
                
                ctx.beginPath();
                ctx.moveTo(x0, y0);
                ctx.lineTo(x1, y1);
                ctx.lineTo(x2, y2);
                ctx.closePath();
                ctx.stroke();
            }
        }
    });
}

// --- UV Island Segmentation & Seam-Preserving Welder ---
function detectUVIslands(geometry) {
    const positionAttr = geometry.attributes.position;
    const uvAttr = geometry.attributes.uv;
    if (!positionAttr || !uvAttr) return [];

    const count = positionAttr.count;
    const indexAttr = geometry.index;
    const numTriangles = indexAttr ? indexAttr.count / 3 : count / 3;

    // Group vertices by (position, uv) to find unique vertex keys in UV-split space
    const vertexKeys = [];
    for (let i = 0; i < count; i++) {
        const px = positionAttr.getX(i).toFixed(5);
        const py = positionAttr.getY(i).toFixed(5);
        const pz = positionAttr.getZ(i).toFixed(5);
        const u = uvAttr.getX(i).toFixed(5);
        const v = uvAttr.getY(i).toFixed(5);
        vertexKeys.push(`${px},${py},${pz}|${u},${v}`);
    }

    // Map vertex key to list of triangle indices that use it
    const vertexToTriangles = new Map();
    for (let i = 0; i < numTriangles; i++) {
        const idx0 = indexAttr ? indexAttr.getX(i * 3) : i * 3;
        const idx1 = indexAttr ? indexAttr.getX(i * 3 + 1) : i * 3 + 1;
        const idx2 = indexAttr ? indexAttr.getX(i * 3 + 2) : i * 3 + 2;

        const keys = [vertexKeys[idx0], vertexKeys[idx1], vertexKeys[idx2]];
        keys.forEach(key => {
            if (!vertexToTriangles.has(key)) {
                vertexToTriangles.set(key, []);
            }
            vertexToTriangles.get(key).push(i);
        });
    }

    // Flood fill to find connected components of triangles
    const visited = new Uint8Array(numTriangles);
    const islands = [];

    for (let i = 0; i < numTriangles; i++) {
        if (visited[i]) continue;

        const islandTriangles = [];
        const queue = [i];
        visited[i] = 1;

        while (queue.length > 0) {
            const triIdx = queue.shift();
            islandTriangles.push(triIdx);

            const idx0 = indexAttr ? indexAttr.getX(triIdx * 3) : triIdx * 3;
            const idx1 = indexAttr ? indexAttr.getX(triIdx * 3 + 1) : triIdx * 3 + 1;
            const idx2 = indexAttr ? indexAttr.getX(triIdx * 3 + 2) : triIdx * 3 + 2;

            const keys = [vertexKeys[idx0], vertexKeys[idx1], vertexKeys[idx2]];
            keys.forEach(key => {
                const adjTris = vertexToTriangles.get(key);
                if (adjTris) {
                    adjTris.forEach(adjIdx => {
                        if (!visited[adjIdx]) {
                            visited[adjIdx] = 1;
                            queue.push(adjIdx);
                        }
                    });
                }
            });
        }

        islands.push(islandTriangles);
    }

    return islands;
}

function weldGeometryByUVIslands(geometry, islands) {
    const positionAttr = geometry.attributes.position;
    const uvAttr = geometry.attributes.uv;
    const hasUV = !!uvAttr;

    const vertexToIsland = new Int32Array(positionAttr.count);
    islands.forEach((island, islandId) => {
        island.forEach(triIdx => {
            vertexToIsland[triIdx * 3] = islandId;
            vertexToIsland[triIdx * 3 + 1] = islandId;
            vertexToIsland[triIdx * 3 + 2] = islandId;
        });
    });

    const uniquePositions = [];
    const uniqueUVs = [];
    const uniqueIslandIds = [];
    
    const positionMap = new Map();
    const indexMapping = new Int32Array(positionAttr.count);

    let uniqueCount = 0;

    for (let i = 0; i < positionAttr.count; i++) {
        const x = positionAttr.getX(i);
        const y = positionAttr.getY(i);
        const z = positionAttr.getZ(i);
        const islandId = vertexToIsland[i];
        
        const key = `${x.toFixed(6)},${y.toFixed(6)},${z.toFixed(6)}|${islandId}`;
        
        if (positionMap.has(key)) {
            indexMapping[i] = positionMap.get(key);
        } else {
            positionMap.set(key, uniqueCount);
            indexMapping[i] = uniqueCount;
            
            uniquePositions.push(x, y, z);
            if (hasUV) {
                uniqueUVs.push(uvAttr.getX(i), uvAttr.getY(i));
            }
            uniqueIslandIds.push(islandId);
            
            uniqueCount++;
        }
    }

    let indices;
    if (geometry.index) {
        const originalIndices = geometry.index.array;
        indices = new Uint32Array(originalIndices.length);
        for (let i = 0; i < originalIndices.length; i++) {
            indices[i] = indexMapping[originalIndices[i]];
        }
    } else {
        indices = new Uint32Array(positionAttr.count);
        for (let i = 0; i < positionAttr.count; i++) {
            indices[i] = indexMapping[i];
        }
    }

    const weldedGeom = new THREE.BufferGeometry();
    weldedGeom.setAttribute('position', new THREE.Float32BufferAttribute(uniquePositions, 3));
    if (hasUV) {
        weldedGeom.setAttribute('uv', new THREE.Float32BufferAttribute(uniqueUVs, 2));
    }
    weldedGeom.setIndex(new THREE.BufferAttribute(indices, 1));
    
    weldedGeom.userData = {
        islandIds: new Int32Array(uniqueIslandIds),
        triangleIslands: vertexToIsland
    };
    
    return weldedGeom;
}

// --- Hierarchy & Model Tree Panel ---
function rebuildHierarchyUI() {
    const treeContainer = document.getElementById('hierarchy-tree');
    if (!treeContainer) return;
    
    treeContainer.innerHTML = '';
    
    piecesHierarchy.forEach((piece) => {
        const meshName = piece.meshName;
        const pieceKey = `piece:${meshName}`;
        let pieceTrans = itemTransforms.get(pieceKey);
        if (!pieceTrans) {
            pieceTrans = { scaleU: 1.0, scaleV: 1.0, offsetU: 0.0, offsetV: 0.0, rotation: 0.0, visible: true, flipV: false };
            itemTransforms.set(pieceKey, pieceTrans);
        }
        
        // Piece Node
        const pieceNode = document.createElement('div');
        pieceNode.className = 'tree-node-piece';
        pieceNode.dataset.type = 'piece';
        pieceNode.dataset.meshName = meshName;
        if (selectedItem && selectedItem.type === 'piece' && selectedItem.meshName === meshName) {
            pieceNode.classList.add('selected');
        }
        
        const pieceLeft = document.createElement('div');
        pieceLeft.className = 'tree-node-left';
        pieceLeft.innerHTML = `<span>📦</span> <span>${meshName}</span>`;
        pieceNode.appendChild(pieceLeft);
        
        // Hover highlight event listeners
        pieceNode.addEventListener('mouseenter', () => {
            hoveredItem = { type: 'piece', meshName: meshName };
            update3DHighlight();
        });
        pieceNode.addEventListener('mouseleave', () => {
            hoveredItem = null;
            update3DHighlight();
        });
        
        // Eye button
        const pieceEye = document.createElement('button');
        pieceEye.className = `visibility-toggle-btn ${pieceTrans.visible ? '' : 'hidden-node'}`;
        pieceEye.innerHTML = pieceTrans.visible ? '👁' : '❌';
        pieceEye.addEventListener('click', (e) => {
            e.stopPropagation();
            pieceTrans.visible = !pieceTrans.visible;
            triggerSimplification();
        });
        pieceNode.appendChild(pieceEye);
        
        pieceNode.addEventListener('click', () => {
            selectedItem = { type: 'piece', meshName: meshName };
            rebuildHierarchyUI();
            drawUVWireframe();
            
            // Sync sliders
            const sliderSU = document.getElementById('editor-scale-u');
            const sliderSV = document.getElementById('editor-scale-v');
            const sliderOU = document.getElementById('editor-offset-u');
            const sliderOV = document.getElementById('editor-offset-v');
            const sliderRot = document.getElementById('editor-rotation');
            
            if (sliderSU) {
                sliderSU.value = pieceTrans.scaleU * 100;
                sliderSV.value = pieceTrans.scaleV * 100;
                sliderOU.value = pieceTrans.offsetU * 100;
                sliderOV.value = pieceTrans.offsetV * 100;
                sliderRot.value = pieceTrans.rotation;
                
                document.getElementById('val-scale-u').innerText = `${pieceTrans.scaleU.toFixed(1)}x`;
                document.getElementById('val-scale-v').innerText = `${pieceTrans.scaleV.toFixed(1)}x`;
                document.getElementById('val-offset-u').innerText = `${pieceTrans.offsetU.toFixed(2)}`;
                document.getElementById('val-offset-v').innerText = `${pieceTrans.offsetV.toFixed(2)}`;
                document.getElementById('val-rotation').innerText = `${pieceTrans.rotation.toFixed(0)}°`;
            }
        });
        
        treeContainer.appendChild(pieceNode);
        
        // Island Nodes
        piece.islands.forEach((island, islandId) => {
            const islandKey = `island:${meshName}:${islandId}`;
            let islandTrans = itemTransforms.get(islandKey);
            if (!islandTrans) {
                islandTrans = { scaleU: 1.0, scaleV: 1.0, offsetU: 0.0, offsetV: 0.0, rotation: 0.0, visible: true, flipV: false };
                itemTransforms.set(islandKey, islandTrans);
            }
            
            const islandNode = document.createElement('div');
            islandNode.className = 'tree-node-island';
            islandNode.dataset.type = 'island';
            islandNode.dataset.meshName = meshName;
            islandNode.dataset.islandId = islandId;
            if (selectedItem && selectedItem.type === 'island' && selectedItem.meshName === meshName && selectedItem.islandId === islandId) {
                islandNode.classList.add('selected');
            }
            
            const islandLeft = document.createElement('div');
            islandLeft.className = 'tree-node-left';
            const faceCount = island.length;
            islandLeft.innerHTML = `<span>🌴</span> <span>Island #${islandId} (${faceCount} poly)</span>`;
            islandNode.appendChild(islandLeft);
            
            // Hover highlight event listeners
            islandNode.addEventListener('mouseenter', () => {
                hoveredItem = { type: 'island', meshName: meshName, islandId: islandId };
                update3DHighlight();
            });
            islandNode.addEventListener('mouseleave', () => {
                hoveredItem = null;
                update3DHighlight();
            });
            
            // Eye button
            const islandEye = document.createElement('button');
            islandEye.className = `visibility-toggle-btn ${islandTrans.visible ? '' : 'hidden-node'}`;
            islandEye.innerHTML = islandTrans.visible ? '👁' : '❌';
            islandEye.addEventListener('click', (e) => {
                e.stopPropagation();
                islandTrans.visible = !islandTrans.visible;
                triggerSimplification();
            });
            islandNode.appendChild(islandEye);
            
            islandNode.addEventListener('click', () => {
                selectedItem = { type: 'island', meshName: meshName, islandId: islandId };
                rebuildHierarchyUI();
                drawUVWireframe();
                
                // Sync sliders
                const sliderSU = document.getElementById('editor-scale-u');
                const sliderSV = document.getElementById('editor-scale-v');
                const sliderOU = document.getElementById('editor-offset-u');
                const sliderOV = document.getElementById('editor-offset-v');
                const sliderRot = document.getElementById('editor-rotation');
                
                if (sliderSU) {
                    sliderSU.value = islandTrans.scaleU * 100;
                    sliderSV.value = islandTrans.scaleV * 100;
                    sliderOU.value = islandTrans.offsetU * 100;
                    sliderOV.value = islandTrans.offsetV * 100;
                    sliderRot.value = islandTrans.rotation;
                    
                    document.getElementById('val-scale-u').innerText = `${islandTrans.scaleU.toFixed(1)}x`;
                    document.getElementById('val-scale-v').innerText = `${islandTrans.scaleV.toFixed(1)}x`;
                    document.getElementById('val-offset-u').innerText = `${islandTrans.offsetU.toFixed(2)}`;
                    document.getElementById('val-offset-v').innerText = `${islandTrans.offsetV.toFixed(2)}`;
                    document.getElementById('val-rotation').innerText = `${islandTrans.rotation.toFixed(0)}°`;
                }
            });
            
            treeContainer.appendChild(islandNode);
        });
    });
    update3DHighlight();
}

// --- 2D Canvas Hit-Testing & Raycasting Helpers ---
function getIslandAtUV(u, v) {
    if (!simplifiedGroup) return null;
    
    let hit = null;
    
    simplifiedGroup.traverse((child) => {
        if (hit) return;
        
        if (child.isMesh && child.geometry) {
            const geom = child.geometry;
            const positionAttr = geom.attributes.position;
            const uvAttr = geom.attributes.uv;
            const indexAttr = geom.index;
            
            if (!uvAttr || !positionAttr) return;
            
            const islandIds = geom.userData.islandIds;
            if (!islandIds) return;
            
            const count = indexAttr ? indexAttr.count : uvAttr.count;
            
            for (let i = 0; i < count; i += 3) {
                const idx0 = indexAttr ? indexAttr.getX(i) : i;
                const idx1 = indexAttr ? indexAttr.getX(i + 1) : i + 1;
                const idx2 = indexAttr ? indexAttr.getX(i + 2) : i + 2;
                
                const u0 = uvAttr.getX(idx0);
                const v0 = uvAttr.getY(idx0);
                const u1 = uvAttr.getX(idx1);
                const v1 = uvAttr.getY(idx1);
                const u2 = uvAttr.getX(idx2);
                const v2 = uvAttr.getY(idx2);
                
                if (isPointInTriangle(u, v, u0, v0, u1, v1, u2, v2)) {
                    const islandId = islandIds[idx0];
                    hit = {
                        meshName: child.name || "Piece",
                        islandId: islandId,
                        triIndex: i / 3
                    };
                    break;
                }
            }
        }
    });
    
    return hit;
}

function isPointInTriangle(px, py, ax, ay, bx, by, cx, cy) {
    const v0x = cx - ax, v0y = cy - ay;
    const v1x = bx - ax, v1y = by - ay;
    const v2x = px - ax, v2y = py - ay;
    
    const dot00 = v0x * v0x + v0y * v0y;
    const dot01 = v0x * v1x + v0y * v1y;
    const dot02 = v0x * v2x + v0y * v2y;
    const dot11 = v1x * v1x + v1y * v1y;
    const dot12 = v1x * v2x + v1y * v2y;
    
    const invDenom = 1 / (dot00 * dot11 - dot01 * dot01);
    const u = (dot11 * dot02 - dot01 * dot12) * invDenom;
    const v = (dot00 * dot12 - dot01 * dot02) * invDenom;
    
    return (u >= 0) && (v >= 0) && (u + v < 1);
}

// --- 3D Viewport Selection Highlight (Holographic Outline/Glow) ---
let active3DHighlight = null;

function update3DHighlight() {
    // 1. Remove previous highlight from its parent
    if (active3DHighlight) {
        if (active3DHighlight.parent) {
            active3DHighlight.parent.remove(active3DHighlight);
        }
        disposeGroup(active3DHighlight);
        active3DHighlight = null;
    }

    // Priority: hovered item takes precedence over the selected item
    const activeItem = hoveredItem || selectedItem;

    if (!activeItem || !simplifiedGroup) return;

    // 2. Find the target mesh in simplifiedGroup
    let targetMesh = null;
    simplifiedGroup.traverse((child) => {
        if (child.isMesh && child.name === activeItem.meshName) {
            targetMesh = child;
        }
    });

    if (!targetMesh) return;

    let highlightGeom = null;

    if (activeItem.type === 'piece') {
        // Use the entire mesh geometry
        highlightGeom = targetMesh.geometry.clone();
    } else if (activeItem.type === 'island') {
        // Build a geometry containing ONLY the triangles of this island from the simplified mesh
        const originalGeom = targetMesh.geometry;
        const positionAttr = originalGeom.attributes.position;
        const indexAttr = originalGeom.index;
        const islandIds = originalGeom.userData.islandIds;
        
        if (!positionAttr || !islandIds) return;

        const vertices = [];
        const indices = [];
        const indexMap = new Map();
        let vertexCount = 0;

        const count = indexAttr ? indexAttr.count : positionAttr.count;

        for (let i = 0; i < count; i += 3) {
            const idx0 = indexAttr ? indexAttr.getX(i) : i;
            const idx1 = indexAttr ? indexAttr.getX(i + 1) : i + 1;
            const idx2 = indexAttr ? indexAttr.getX(i + 2) : i + 2;

            // Welded vertices on a single face belong to the same UV island. Check the first vertex.
            const islandId = islandIds[idx0];

            if (islandId === activeItem.islandId) {
                const triVerts = [idx0, idx1, idx2];
                const newTriIndices = [];

                triVerts.forEach(vIdx => {
                    if (indexMap.has(vIdx)) {
                        newTriIndices.push(indexMap.get(vIdx));
                    } else {
                        indexMap.set(vIdx, vertexCount);
                        newTriIndices.push(vertexCount);
                        
                        vertices.push(
                            positionAttr.getX(vIdx),
                            positionAttr.getY(vIdx),
                            positionAttr.getZ(vIdx)
                        );
                        vertexCount++;
                    }
                });

                indices.push(newTriIndices[0], newTriIndices[1], newTriIndices[2]);
            }
        }

        if (vertices.length === 0) return;

        highlightGeom = new THREE.BufferGeometry();
        highlightGeom.setAttribute('position', new THREE.Float32BufferAttribute(vertices, 3));
        highlightGeom.setIndex(indices);
    }

    if (!highlightGeom) return;

    // Bright cyan wireframe outline material (mesh lines)
    const wireMat = new THREE.MeshBasicMaterial({
        color: 0x00ffff, // High-contrast cyan
        wireframe: true,
        transparent: true,
        opacity: 0.9, // Semi-opaque wireframe lines
        depthWrite: false,
        polygonOffset: true,
        polygonOffsetFactor: -4, // Pull forward significantly to stay on top
        polygonOffsetUnits: -4
    });

    const wireMesh = new THREE.Mesh(highlightGeom, wireMat);
    wireMesh.name = "active_3d_highlight_wireframe";

    // Add directly as a child of the target mesh so it inherits all parent transformations perfectly!
    targetMesh.add(wireMesh);
    active3DHighlight = wireMesh;
}

// --- Bidirectional Viewport Sync Helper ---
function syncListHoverState(meshName, islandId) {
    const nodes = document.querySelectorAll('.tree-node-island, .tree-node-piece');
    nodes.forEach(node => node.classList.remove('hovered'));

    if (meshName === null) return;

    let targetNode = null;
    if (islandId !== null && islandId !== undefined) {
        targetNode = document.querySelector(`.tree-node-island[data-mesh-name="${meshName}"][data-island-id="${islandId}"]`);
    } else {
        targetNode = document.querySelector(`.tree-node-piece[data-mesh-name="${meshName}"]`);
    }

    if (targetNode) {
        targetNode.classList.add('hovered');
        targetNode.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
    }
}


