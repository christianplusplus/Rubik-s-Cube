/**
 * Rubik's Cube
 * CS 371
 * Professor Thomas Naps
 * Authors: Christian Wendlandt & Tariq Anjum
 * Version: 2019.3.22
 *
 * This code is for 3D Rubik's Cube
 * HTML buttons are used to manipulate and rotate the cube.
 *
 *
 * For gee-golly-whiz points:
 *     The magic button enables a mapping for the cubie sides.
 *     Each visible side is offset from the real cube and uses
 *     a circle instead of square. Inner sides are hidden.
 *
 *     We also added an unscramble button.
 */

var gl;
var canvas;
var program;

var g_matrixStack = []; // Stack for storing a matrix
var modelViewMatrix = mat4();	// model-view matrix
var projectionMatrix;		// Projection matrix
var modelViewMatrixLoc, projectionMatrixLoc, magicViewMatrix;
var numVertices = 24; //(6 faces)(4 vertices for triangle-fan comprising each fan)
var verticesPerFace = 4;

var points = [];		// Coordinates geneated for all cubie faces
var colors = [];		// Associated colors

var magicPoints = [];
var magicColors = [];

var vBuffer, cBuffer;

var myCube = new Rubik3x3();	// Rubik cube "object" with operations as documented in
// rubik-helper.js

// Starting coordinates (that is, before transformations) for each
// cubie
var vertices = [
    vec4(-0.5,-0.5, 0.5, 1.0),  // vertex 0
    vec4(-0.5, 0.5, 0.5, 1.0),  // 1
    vec4( 0.5, 0.5, 0.5, 1.0),  // 2
    vec4( 0.5,-0.5, 0.5, 1.0),  // 3
    vec4(-0.5,-0.5,-0.5, 1.0),  // 4
    vec4(-0.5, 0.5,-0.5, 1.0),  // 5
    vec4( 0.5, 0.5,-0.5, 1.0),  // 6
    vec4( 0.5,-0.5,-0.5, 1.0)   // 7
];

// RGBA colors for cubies
var vertexColors = [
    vec4(0.5,0.5,0.5,1.0),   // 0  hidden (gray)                     
    vec4(1.0,0.0,0.0,1.0),   // 1  red           RIGHT face  (x+)  
    vec4(1.0,0.35,0.0,1.0),  // 2  orange        LEFT face   (x-)
    vec4(0.0,0.0,1.0,1.0),   // 3  blue          UP face     (y+)
    vec4(0.0,1.0,0.0,1.0),   // 4  green         DOWN face   (y-)
    vec4(1.0,1.0,1.0,1.0),   // 5  white         FRONT face  (z+)
    vec4(1.0,1.0,0.0,1.0)    // 6  yellow        BACK face   (z-)  
];

var trans = [ 			// Translation from origin for each cubie
    [-1.0, 1.0, 1.0],
    [ 0.0, 1.0, 1.0],
    [ 1.0, 1.0, 1.0],
    [-1.0, 0.0, 1.0],
    [ 0.0, 0.0, 1.0],
    [ 1.0, 0.0, 1.0],
    [-1.0,-1.0, 1.0],
    [ 0.0,-1.0, 1.0],
    [ 1.0,-1.0, 1.0],
    
    [-1.0, 1.0, 0.0],
    [ 0.0, 1.0, 0.0],
    [ 1.0, 1.0, 0.0],
    [-1.0, 0.0, 0.0],
    [ 1.0, 0.0, 0.0],
    [-1.0,-1.0, 0.0],
    [ 0.0,-1.0, 0.0],
    [ 1.0,-1.0, 0.0],
    
    [-1.0, 1.0,-1.0],
    [ 0.0, 1.0,-1.0],
    [ 1.0, 1.0,-1.0],
    [-1.0, 0.0,-1.0],
    [ 0.0, 0.0,-1.0],
    [ 1.0, 0.0,-1.0],
    [-1.0,-1.0,-1.0],
    [ 0.0,-1.0,-1.0],
    [ 1.0,-1.0,-1.0]
];

// accum_rotation is an array of 26 mat4's that is not currently used
// in your starter code.  However, the intent is that
// accum_rotation[i] provide the matrix that encompasses the entire
// accumulation of R,r,L,l,U,u,D,d,F,f,B,b rotations that have been
// triggered by user interactions at any point in time
var accum_rotation = [
    mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(),
    mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(),
    mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(),
    mat4(), mat4()
];

var viewer = [7.0, 3.0, 7.0]; // initial viewer location
var magicViewer = [10,10,10]; // magic viewer location

const FRAMES_PER_ROTATION = 45; // number of frames per rotation.
const MAGIC_OFFSET = 2.5; // how far away each side is away from the real cube in magic mode.
const MAGIC_SCALE = 1; // how far adjacent sides are to eachother in magic mode.
var modelRotationMatrix = mat4(); // rotates the entire cube.
var timer = 0; // a timer utility variable used for animation.
var cubies = []; // the list of cubies that are being rotated.
var rotationFunction; // a function that is selected to rotate the cubies.
var magic = false; // flag for magic button.

window.onload = function init()
{
    canvas = document.getElementById( "gl-canvas" );
    
    gl = WebGLUtils.setupWebGL( canvas );
    //gl = WebGLDebugUtils.makeDebugContext( canvas.getContext("webgl") ); // For debugging
    if ( !gl ) { alert( "WebGL isn't available" );}
    
    generateVertsAndColors();
    generateMagicVertsAndColors();
    
    gl.viewport( 0, 0, canvas.width, canvas.height );
    gl.clearColor( 0.0, 0.0, 0.0, 1.0 );
    // Enable depth testing 
    gl.enable(gl.DEPTH_TEST);

    // Polygon offset avoids "z-fighting" between triangles and line
    // loops, ensuring lines will be in front of filled triangles
    gl.depthFunc(gl.LEQUAL);	
    gl.enable(gl.POLYGON_OFFSET_FILL);
    gl.polygonOffset(1.0, 2.0);

    //  Load shaders and initialize attribute buffers

    program = initShaders( gl, "vertex-shader", "fragment-shader" );
    gl.useProgram( program );

    // Load the data into the GPU and associate our shader variables
    // with our data buffer

    vBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, vBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, flatten(points), gl.STATIC_DRAW);

    var vPosition = gl.getAttribLocation(program, "vPosition");
    gl.vertexAttribPointer(vPosition, 4, gl.FLOAT, false, 0, 0);
    gl.enableVertexAttribArray(vPosition);    

    cBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, cBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, flatten(colors), gl.STATIC_DRAW);

    var vColor = gl.getAttribLocation(program, "vColor");
    gl.vertexAttribPointer(vColor, 4, gl.FLOAT, false, 0, 0);
    gl.enableVertexAttribArray(vColor);
    
    projectionMatrix = perspective(45.0, canvas.width / canvas.height, 2.0, 30.0);
    modelViewMatrix = lookAt(viewer, vec3(0.0, 0.0, 0.0), vec3(0.0, 1.0, 0.0));
    magicViewMatrix = lookAt(magicViewer, vec3(0.0, 0.0, 0.0), vec3(0.0, 1.0, 0.0));

    projectionMatrixLoc = gl.getUniformLocation(program, "projectionMatrix");
    modelViewMatrixLoc = gl.getUniformLocation(program, "modelViewMatrix");
    offsetMatrixLoc = gl.getUniformLocation(program, "offsetMatrix");
    accumulationMatrixLoc = gl.getUniformLocation(program, "accumulationMatrix");
    modelRotationMatrixLoc = gl.getUniformLocation(program, "modelRotationMatrix");

    gl.uniformMatrix4fv(projectionMatrixLoc, false, flatten(projectionMatrix));
    gl.uniformMatrix4fv(modelViewMatrixLoc, false, flatten(modelViewMatrix));
    gl.uniformMatrix4fv(offsetMatrixLoc, false, flatten(mat4()));
    
    // Button event-handlers for rotation will need to be written by
    // you.  For the sake of your code's clarity, these event handlers
    // must not be written in their entirety here in window.onload but
    // instead they should defer what they do to functions that are
    // written outside of window.onload and merely called here.
    // Failing to follow this requirement will mean that your code
    // will be impossible to read, and substantial style points will
    // therefore be deducted.
    document.getElementById("xButton").onclick = function()
    {
	    modelRotationMatrix = mult(rotateX(18), modelRotationMatrix);
        render();
    };
    document.getElementById("yButton").onclick = function()
    {
        modelRotationMatrix = mult(rotateY(18), modelRotationMatrix);
        render();
    };
    document.getElementById("zButton").onclick = function()
    {
        modelRotationMatrix = mult(rotateZ(18), modelRotationMatrix);
        render();
    };
    document.getElementById("ResetButton").onclick = function()
    {
        modelRotationMatrix = mat4();
        render();
    };
    document.getElementById("RandomButton").onclick = function()
    {
        incrementalRotation(myCube.getRandomAction());
    };
    document.getElementById("RButton").onclick = function(){incrementalRotation("R");};
    document.getElementById("rButton").onclick = function(){incrementalRotation("r");};
    document.getElementById("LButton").onclick = function(){incrementalRotation("L");};
    document.getElementById("lButton").onclick = function(){incrementalRotation("l");};
    document.getElementById("UButton").onclick = function(){incrementalRotation("U");};
    document.getElementById("uButton").onclick = function(){incrementalRotation("u");};
    document.getElementById("DButton").onclick = function(){incrementalRotation("D");};
    document.getElementById("dButton").onclick = function(){incrementalRotation("d");};
    document.getElementById("FButton").onclick = function(){incrementalRotation("F");};
    document.getElementById("fButton").onclick = function(){incrementalRotation("f");};
    document.getElementById("BButton").onclick = function(){incrementalRotation("B");};
    document.getElementById("bButton").onclick = function(){incrementalRotation("b");};
    document.getElementById("ScrambleButton").onclick = function(){scramble();};
    document.getElementById("unScrambleButton").onclick = function(){unscramble();};
    document.getElementById("magic").onclick = function(){doMagic();};
    
    render();
};

//MODIFIED
// Points and colors for one face of a cubie
function cubie_side(a, b, c , d, col, i)
{
    points.push(mult(translate(trans[i]),vertices[a]));
    points.push(mult(translate(trans[i]),vertices[b]));
    points.push(mult(translate(trans[i]),vertices[c]));
    points.push(mult(translate(trans[i]),vertices[d]));
    colors.push(vertexColors[col],vertexColors[col],
		    vertexColors[col],vertexColors[col]);
};

//MODIFIED
// Generate vertices for cubie i
function cubie(i)
{
    cubie_side(2,3,7,6,myCube.getCubieColor(myCube.cubie_at_position[i])[0], i);
    cubie_side(0,1,5,4,myCube.getCubieColor(myCube.cubie_at_position[i])[1], i);
    cubie_side(1,2,6,5,myCube.getCubieColor(myCube.cubie_at_position[i])[2], i);
    cubie_side(0,4,7,3,myCube.getCubieColor(myCube.cubie_at_position[i])[3], i);
    cubie_side(0,3,2,1,myCube.getCubieColor(myCube.cubie_at_position[i])[4], i);
    cubie_side(4,5,6,7,myCube.getCubieColor(myCube.cubie_at_position[i])[5], i);
}

// Generate all vertex data for entire Rubik's cube
function generateVertsAndColors()
{
    for (var i = 0; i < myCube.TOTAL_CUBIES; i++)
    {
	    cubie(i);
    }
};

// Points and colors for one face of a magic cubie
// i : the ID of the cubie
// col : the color of the side to be drawn
function magicCubieSide(col, i)
{
    magicVertices(col).forEach(function(vertex)
    {
        magicPoints.push(mult(translate(trans[i]),vertex));
        magicColors.push(vertexColors[col]);
    });
};

// Generate magic vertices for cubie i
// i : the ID of the cubie
function magicCubie(i)
{
    magicCubieSide(myCube.getCubieColor(myCube.cubie_at_position[i])[0], i);
    magicCubieSide(myCube.getCubieColor(myCube.cubie_at_position[i])[1], i);
    magicCubieSide(myCube.getCubieColor(myCube.cubie_at_position[i])[2], i);
    magicCubieSide(myCube.getCubieColor(myCube.cubie_at_position[i])[3], i);
    magicCubieSide(myCube.getCubieColor(myCube.cubie_at_position[i])[4], i);
    magicCubieSide(myCube.getCubieColor(myCube.cubie_at_position[i])[5], i);
}

// Generate all magic vertex data for entire Rubik's cube
function generateMagicVertsAndColors()
{
    for (var i = 0; i < myCube.TOTAL_CUBIES; i++)
        magicCubie(i);
};

// Renders the cube
function render()
{
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    var offsetMatrix, scaleMatrix;
    for (var i = 0; i < (magic ? magicPoints.length : points.length); i = i + numVertices)
    {
        var c = i / numVertices;
        gl.uniformMatrix4fv(accumulationMatrixLoc, false, flatten(accum_rotation[c]));
        gl.uniformMatrix4fv(modelRotationMatrixLoc, false, flatten(modelRotationMatrix));
        if(magic)
        {
            scaleMatrix = mult(scalem(MAGIC_SCALE,MAGIC_SCALE,MAGIC_SCALE), translate(trans[c]));
            scaleMatrix = mult(translate(negate(trans[c])), scaleMatrix);
        }
	    for(var j = i; j < i + numVertices; j = j + verticesPerFace)
        {
            var side = (j-i)/verticesPerFace;
            if(magic)
            {
                if(myCube.getCubieColor(c)[side] == 0)
                    continue;
                switch(myCube.getCubieColor(c)[side])
                {
                    case 1:
                        offsetMatrix = mult(translate(MAGIC_OFFSET, 0, 0), scaleMatrix);
                        break;
                    case 2:
                        offsetMatrix = mult(translate(-MAGIC_OFFSET, 0, 0), scaleMatrix);
                        break;
                    case 3:
                        offsetMatrix = mult(translate(0, MAGIC_OFFSET, 0), scaleMatrix);
                        break;
                    case 4:
                        offsetMatrix = mult(translate(0, -MAGIC_OFFSET, 0), scaleMatrix);
                        break;
                    case 5:
                        offsetMatrix = mult(translate(0, 0, MAGIC_OFFSET), scaleMatrix);
                        break;
                    case 6:
                        offsetMatrix = mult(translate(0, 0, -MAGIC_OFFSET), scaleMatrix);
                        break;
                }
                gl.uniformMatrix4fv(offsetMatrixLoc, false, flatten(offsetMatrix));
            }
            else
            {
                gl.uniform1i(gl.getUniformLocation(program, "outline_mode"), 1);
                gl.drawArrays(gl.LINE_LOOP, j, verticesPerFace);
                gl.uniform1i(gl.getUniformLocation(program, "outline_mode"), 0);
            }
            gl.drawArrays(gl.TRIANGLE_FAN, j, verticesPerFace);
	    }
    };
    gl.uniformMatrix4fv(offsetMatrixLoc, false, flatten(mat4()));
    if(timer > 0)
    {
        timer--;
        cubies.forEach(rotationFunction);
        requestAnimFrame(render);
    }
    else
        disableButtons(false);
}

// selects the cubies to be rotated, selects a rotation function, disables UI buttons,
//     and sets the timer so that it rotates 90 degrees.
// rotation : a character specifying which rotation to perform.
function incrementalRotation(rotation)
{
    cubies = myCube.performAction(rotation);
    var rotationMatrix;
    switch(rotation)
    {
        case "R":
            rotationMatrix = rotateX(-90/FRAMES_PER_ROTATION);
            break;
        case "r":
            rotationMatrix = rotateX(90/FRAMES_PER_ROTATION);
            break;
        case "L":
            rotationMatrix = rotateX(90/FRAMES_PER_ROTATION);
            break;
        case "l":
            rotationMatrix = rotateX(-90/FRAMES_PER_ROTATION);
            break;
        case "F":
            rotationMatrix = rotateZ(-90/FRAMES_PER_ROTATION);
            break;
        case "f":
            rotationMatrix = rotateZ(90/FRAMES_PER_ROTATION);
            break;
        case "B":
            rotationMatrix = rotateZ(90/FRAMES_PER_ROTATION);
            break;
        case "b":
            rotationMatrix = rotateZ(-90/FRAMES_PER_ROTATION);
            break;
        case "U":
            rotationMatrix = rotateY(-90/FRAMES_PER_ROTATION);
            break;
        case "u":
            rotationMatrix = rotateY(90/FRAMES_PER_ROTATION);
            break;
        case "D":
            rotationMatrix = rotateY(90/FRAMES_PER_ROTATION);
            break;
        case "d":
            rotationMatrix = rotateY(-90/FRAMES_PER_ROTATION);
            break;
    }
    rotationFunction = function(piece)
    {
        accum_rotation[myCube.cubie_at_position[piece]] =
                mult(rotationMatrix, accum_rotation[myCube.cubie_at_position[piece]]);
    };
    timer = FRAMES_PER_ROTATION;
    disableButtons(true);
    render();
}

// selects the cubies to be rotated, selects a rotation function, but with
//     no inbetween frames.
// rotation : a character specifying which rotation to perform.
function noRenderRotation(rotation)
{
    cubies = myCube.performAction(rotation);
    var rotationMatrix;
    switch(rotation)
    {
        case "R":
            rotationMatrix = rotateX(-90);
            break;
        case "r":
            rotationMatrix = rotateX(90);
            break;
        case "L":
            rotationMatrix = rotateX(90);
            break;
        case "l":
            rotationMatrix = rotateX(-90);
            break;
        case "F":
            rotationMatrix = rotateZ(-90);
            break;
        case "f":
            rotationMatrix = rotateZ(90);
            break;
        case "B":
            rotationMatrix = rotateZ(90);
            break;
        case "b":
            rotationMatrix = rotateZ(-90);
            break;
        case "U":
            rotationMatrix = rotateY(-90);
            break;
        case "u":
            rotationMatrix = rotateY(90);
            break;
        case "D":
            rotationMatrix = rotateY(90);
            break;
        case "d":
            rotationMatrix = rotateY(-90);
            break;
    }
    rotationFunction = function(piece){accum_rotation[myCube.cubie_at_position[piece]] =
            mult(rotationMatrix, accum_rotation[myCube.cubie_at_position[piece]]);};
}

// disables all HTML rotation buttons.
// bool : set true to disable, set false to enable.
function disableButtons(bool)
{
    document.getElementById("RButton").disabled = bool;
    document.getElementById("rButton").disabled = bool;
    document.getElementById("LButton").disabled = bool;
    document.getElementById("lButton").disabled = bool;
    document.getElementById("UButton").disabled = bool;
    document.getElementById("uButton").disabled = bool;
    document.getElementById("DButton").disabled = bool;
    document.getElementById("dButton").disabled = bool;
    document.getElementById("FButton").disabled = bool;
    document.getElementById("fButton").disabled = bool;
    document.getElementById("BButton").disabled = bool;
    document.getElementById("bButton").disabled = bool;
    document.getElementById("RandomButton").disabled = bool;
    document.getElementById("ScrambleButton").disabled = bool;
    document.getElementById("unScrambleButton").disabled = bool;
}

// Gives the circular virtices for a given face color.
// face : the face color id. non-surface points are set to the origin.
function magicVertices(face)
{
    var faceVertices = [];
    for(var theta = 0; theta < 360; theta += 10)
    switch(face)
    {
        case 0:
            faceVertices.push([0,0,0,1]);
            break;
        case 1:
            faceVertices.push([.5,.5*Math.cos(radians(theta)),.5*Math.sin(radians(theta)),1]);
            break;
        case 2:
            faceVertices.push([-.5,.5*Math.cos(radians(theta)),.5*Math.sin(radians(theta)),1]);
            break;
        case 3:
            faceVertices.push([.5*Math.cos(radians(theta)),.5,.5*Math.sin(radians(theta)),1]);
            break;
        case 4:
            faceVertices.push([.5*Math.cos(radians(theta)),-.5,.5*Math.sin(radians(theta)),1]);
            break;
        case 5:
            faceVertices.push([.5*Math.cos(radians(theta)),.5*Math.sin(radians(theta)),.5,1]);
            break;
        case 6:
            faceVertices.push([.5*Math.cos(radians(theta)),.5*Math.sin(radians(theta)),-.5,1]);
            break;
    }
    return faceVertices;
}

// scrambles the cube.
function scramble()
{
    for(var i = 0; i < 100; i++)
    {
        noRenderRotation(myCube.getRandomAction());
        cubies.forEach(rotationFunction);
    }
    render();
}

// unscrambles the cube.
function unscramble()
{
    myCube = new Rubik3x3();
    accum_rotation = [
        mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(),
        mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(),
        mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(), mat4(),
        mat4(), mat4()
    ];
    render();
}

// switch between regular and magic mode.
function doMagic()
{
    if(magic)
    {
        gl.uniformMatrix4fv(modelViewMatrixLoc, false, flatten(modelViewMatrix));
        gl.bindBuffer(gl.ARRAY_BUFFER, vBuffer);
        gl.bufferData(gl.ARRAY_BUFFER, flatten(points), gl.STATIC_DRAW);
        gl.bindBuffer(gl.ARRAY_BUFFER, cBuffer);
        gl.bufferData(gl.ARRAY_BUFFER, flatten(colors), gl.STATIC_DRAW);
        numVertices = 24;
        verticesPerFace = 4;   
    }
    else
    {
        gl.uniformMatrix4fv(modelViewMatrixLoc, false, flatten(magicViewMatrix));
        gl.bindBuffer(gl.ARRAY_BUFFER, vBuffer);
        gl.bufferData(gl.ARRAY_BUFFER, flatten(magicPoints), gl.STATIC_DRAW);
        gl.bindBuffer(gl.ARRAY_BUFFER, cBuffer);
        gl.bufferData(gl.ARRAY_BUFFER, flatten(magicColors), gl.STATIC_DRAW);
        numVertices = 216;
        verticesPerFace = 36;
    }
    magic = !magic;
    render();
}
