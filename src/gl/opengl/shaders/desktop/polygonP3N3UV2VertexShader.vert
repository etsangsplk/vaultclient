#version 330
#extension GL_ARB_separate_shader_objects : require

out gl_PerVertex
{
    vec4 gl_Position;
};

layout(std140) uniform type_u_EveryObject
{
    layout(row_major) mat4 u_worldViewProjectionMatrix;
    layout(row_major) mat4 u_worldMatrix;
    vec4 u_colour;
    vec4 u_objectInfo;
} u_EveryObject;

layout(location = 0) in vec3 in_var_POSITION;
layout(location = 1) in vec3 in_var_NORMAL;
layout(location = 2) in vec2 in_var_TEXCOORD0;
layout(location = 0) out vec2 out_var_TEXCOORD0;
layout(location = 1) out vec3 out_var_NORMAL;
layout(location = 2) out vec4 out_var_COLOR0;
layout(location = 3) out vec2 out_var_TEXCOORD1;
layout(location = 4) out vec2 out_var_TEXCOORD2;

vec2 _37;

void main()
{
    vec4 _57 = vec4(in_var_POSITION, 1.0) * u_EveryObject.u_worldViewProjectionMatrix;
    vec2 _62 = _37;
    _62.x = 1.0 + _57.w;
    vec2 _65 = _37;
    _65.x = u_EveryObject.u_objectInfo.x;
    gl_Position = _57;
    out_var_TEXCOORD0 = in_var_TEXCOORD0;
    out_var_NORMAL = normalize((vec4(in_var_NORMAL, 0.0) * u_EveryObject.u_worldMatrix).xyz);
    out_var_COLOR0 = u_EveryObject.u_colour;
    out_var_TEXCOORD1 = _62;
    out_var_TEXCOORD2 = _65;
}

