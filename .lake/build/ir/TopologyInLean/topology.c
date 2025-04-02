// Lean compiler output
// Module: TopologyInLean.topology
// Imports: Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_empty__topology;
LEAN_EXPORT lean_object* l_product__topology___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Topology_open__sets__are__open__basis___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_discrete__topology(lean_object*);
LEAN_EXPORT lean_object* l_exam__problem__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_final__topology(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_indiscrete__topology(lean_object*);
LEAN_EXPORT lean_object* l_final__topology___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_product__topology(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_exam__problem__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_point__topology;
LEAN_EXPORT lean_object* l_Topology_open__sets__are__open__basis___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Topology_from__basis__sets(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Topology_open__sets__are__open__basis(lean_object*);
LEAN_EXPORT lean_object* l_discrete__topology(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_indiscrete__topology(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_empty__topology() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_point__topology() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Topology_open__sets__are__open__basis___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Topology_open__sets__are__open__basis(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Topology_open__sets__are__open__basis___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Topology_open__sets__are__open__basis___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Topology_open__sets__are__open__basis___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Topology_from__basis__sets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_final__topology(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_final__topology___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_final__topology(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_exam__problem__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_exam__problem__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_exam__problem__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_product__topology(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_product__topology___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_product__topology(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TopologyInLean_topology(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_empty__topology = _init_l_empty__topology();
lean_mark_persistent(l_empty__topology);
l_point__topology = _init_l_point__topology();
lean_mark_persistent(l_point__topology);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
