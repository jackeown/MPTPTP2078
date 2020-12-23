%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:09 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   65 (  65 expanded)
%              Number of leaves         :   65 (  65 expanded)
%              Depth                    :    0
%              Number of atoms          :  243 ( 243 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u29,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u39,axiom,
    ( ~ v4_orders_2(X0)
    | ~ r1_lattice3(X0,X3,X2)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X3,X1) )).

cnf(u163,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u102,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0)) )).

cnf(u162,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0)) )).

cnf(u70,negated_conjecture,
    ( r1_orders_2(sK0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2),sK3(sK0,X0,sK2))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,sK2) )).

cnf(u113,negated_conjecture,
    ( r1_orders_2(sK0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2),sK3(sK0,X2,sK2))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X2,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | r1_lattice3(sK0,X2,sK2) )).

cnf(u52,negated_conjecture,
    ( ~ r1_orders_2(sK0,X2,X1)
    | ~ r1_lattice3(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,X2) )).

cnf(u38,axiom,
    ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u142,negated_conjecture,
    ( r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) )).

cnf(u184,negated_conjecture,
    ( r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) )).

cnf(u62,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u87,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u82,negated_conjecture,
    ( r1_lattice3(sK0,sK1,sK2)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u53,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK2)
    | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0)) )).

cnf(u33,negated_conjecture,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | r1_lattice3(sK0,sK1,sK2) )).

cnf(u166,negated_conjecture,
    ( ~ r1_lattice3(sK0,X0,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | r1_lattice3(sK0,X0,sK2) )).

cnf(u116,negated_conjecture,
    ( ~ r1_lattice3(sK0,X1,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | r1_lattice3(sK0,X1,sK2) )).

cnf(u169,negated_conjecture,
    ( ~ r1_lattice3(sK0,X1,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | r1_lattice3(sK0,X1,sK2) )).

cnf(u91,negated_conjecture,
    ( ~ r1_lattice3(sK0,X1,sK3(sK0,X0,sK2))
    | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u135,negated_conjecture,
    ( ~ r1_lattice3(sK0,X1,sK3(sK0,X0,sK2))
    | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,sK2)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u54,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK1,sK2)
    | m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0)) )).

cnf(u34,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ r1_lattice3(sK0,sK1,sK2) )).

cnf(u61,negated_conjecture,
    ( ~ r1_lattice3(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK3(sK0,X0,sK2))
    | r1_lattice3(sK0,X0,sK2) )).

cnf(u93,negated_conjecture,
    ( ~ r1_lattice3(sK0,X0,X1)
    | r1_orders_2(sK0,X1,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u153,negated_conjecture,
    ( ~ r1_lattice3(sK0,X0,X1)
    | r1_orders_2(sK0,X1,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u72,negated_conjecture,
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),X0)
    | r1_orders_2(sK0,X0,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK2) )).

cnf(u119,negated_conjecture,
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),X0)
    | r1_orders_2(sK0,X0,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u171,negated_conjecture,
    ( ~ r1_lattice3(sK0,u1_struct_0(sK0),X0)
    | r1_orders_2(sK0,X0,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u30,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u124,negated_conjecture,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | r1_orders_2(X0,X1,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(X0))
    | ~ r1_lattice3(X0,u1_struct_0(sK0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u104,negated_conjecture,
    ( ~ l1_orders_2(X1)
    | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | r1_orders_2(X1,X2,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | ~ m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u94,negated_conjecture,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_orders_2(X0,X1,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | ~ m1_subset_1(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(X0))
    | ~ r1_lattice3(X0,u1_struct_0(sK0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u66,negated_conjecture,
    ( ~ l1_orders_2(X1)
    | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | r1_orders_2(X1,X2,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)))
    | ~ m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(X1))
    | ~ r1_lattice3(X1,X0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u57,negated_conjecture,
    ( ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(X0))
    | ~ r1_lattice3(X0,u1_struct_0(sK0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_lattice3(sK0,sK1,sK2) )).

cnf(u49,negated_conjecture,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(sK3(sK0,X2,sK2),u1_struct_0(X0))
    | ~ r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,sK3(sK0,X2,sK2))
    | r1_lattice3(sK0,X2,sK2) )).

cnf(u37,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u36,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u86,negated_conjecture,
    ( r2_hidden(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u120,negated_conjecture,
    ( r2_hidden(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u63,negated_conjecture,
    ( r2_hidden(sK3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X1)
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u88,negated_conjecture,
    ( r2_hidden(sK3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X1)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u56,negated_conjecture,
    ( r2_hidden(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK2) )).

cnf(u46,negated_conjecture,
    ( r2_hidden(sK3(sK0,X0,sK2),X0)
    | r1_lattice3(sK0,X0,sK2) )).

cnf(u41,axiom,
    ( ~ r2_hidden(X2,X1)
    | r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u42,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u35,axiom,
    ( ~ r2_hidden(X4,X1)
    | r1_orders_2(X0,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u55,negated_conjecture,
    ( m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u84,negated_conjecture,
    ( m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u31,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u58,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2))
    | r1_lattice3(sK0,sK1,sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),X2) )).

cnf(u59,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X3))
    | r2_hidden(sK3(sK0,sK1,sK2),X3)
    | r1_lattice3(sK0,sK1,sK2) )).

cnf(u95,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X2) )).

cnf(u96,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X3))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X3)
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u125,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X2) )).

cnf(u126,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X3))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X3)
    | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) )).

cnf(u47,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_lattice3(sK0,X0,sK2)
    | m1_subset_1(sK3(sK0,X0,sK2),X1) )).

cnf(u48,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | r2_hidden(sK3(sK0,X2,sK2),X3)
    | r1_lattice3(sK0,X2,sK2) )).

cnf(u67,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | r1_lattice3(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X4) )).

cnf(u68,negated_conjecture,
    ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
    | r1_lattice3(sK0,X5,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | r2_hidden(sK3(sK0,X5,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X6)
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u105,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | r1_lattice3(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X4) )).

cnf(u106,negated_conjecture,
    ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
    | r1_lattice3(sK0,X5,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))
    | r2_hidden(sK3(sK0,X5,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X6)
    | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u44,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,X0,X1),X0)
    | r1_lattice3(sK0,X0,X1) )).

cnf(u45,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (6563)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (6566)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (6557)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (6578)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.48  % (6570)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (6577)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.49  % (6562)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (6559)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.49  % (6562)Refutation not found, incomplete strategy% (6562)------------------------------
% 0.21/0.49  % (6562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6562)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6562)Memory used [KB]: 895
% 0.21/0.49  % (6562)Time elapsed: 0.070 s
% 0.21/0.49  % (6562)------------------------------
% 0.21/0.49  % (6562)------------------------------
% 0.21/0.49  % (6572)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.49  % (6561)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (6572)Refutation not found, incomplete strategy% (6572)------------------------------
% 0.21/0.49  % (6572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (6575)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.50  % (6576)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (6565)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.50  % (6575)Refutation not found, incomplete strategy% (6575)------------------------------
% 0.21/0.50  % (6575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6575)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6575)Memory used [KB]: 9850
% 0.21/0.50  % (6575)Time elapsed: 0.087 s
% 0.21/0.50  % (6575)------------------------------
% 0.21/0.50  % (6575)------------------------------
% 0.21/0.50  % (6572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6572)Memory used [KB]: 5373
% 0.21/0.50  % (6572)Time elapsed: 0.086 s
% 0.21/0.50  % (6572)------------------------------
% 0.21/0.50  % (6572)------------------------------
% 0.21/0.50  % (6558)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.50  % (6573)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  % (6573)Refutation not found, incomplete strategy% (6573)------------------------------
% 0.21/0.50  % (6573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6573)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6573)Memory used [KB]: 895
% 0.21/0.50  % (6573)Time elapsed: 0.072 s
% 0.21/0.50  % (6573)------------------------------
% 0.21/0.50  % (6573)------------------------------
% 0.21/0.50  % (6560)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.51  % (6560)Refutation not found, incomplete strategy% (6560)------------------------------
% 0.21/0.51  % (6560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6560)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6560)Memory used [KB]: 9850
% 0.21/0.51  % (6560)Time elapsed: 0.089 s
% 0.21/0.51  % (6560)------------------------------
% 0.21/0.51  % (6560)------------------------------
% 0.21/0.51  % (6574)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.51  % (6568)WARNING: option uwaf not known.
% 0.21/0.51  % (6578)# SZS output start Saturation.
% 0.21/0.51  cnf(u29,negated_conjecture,
% 0.21/0.51      v4_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,axiom,
% 0.21/0.51      ~v4_orders_2(X0) | ~r1_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X3,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u163,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK2,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u102,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK2,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u162,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK2,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u70,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2),sK3(sK0,X0,sK2)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u113,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2),sK3(sK0,X2,sK2)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X2,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | r1_lattice3(sK0,X2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u52,negated_conjecture,
% 0.21/0.51      ~r1_orders_2(sK0,X2,X1) | ~r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,axiom,
% 0.21/0.51      ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u142,negated_conjecture,
% 0.21/0.51      r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u184,negated_conjecture,
% 0.21/0.51      r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u62,negated_conjecture,
% 0.21/0.51      r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u87,negated_conjecture,
% 0.21/0.51      r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u82,negated_conjecture,
% 0.21/0.51      r1_lattice3(sK0,sK1,sK2) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u53,negated_conjecture,
% 0.21/0.51      r1_lattice3(sK0,X0,sK2) | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,negated_conjecture,
% 0.21/0.51      r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2) | r1_lattice3(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u166,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,X0,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r1_lattice3(sK0,X0,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u116,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,X1,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r1_lattice3(sK0,X1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u169,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,X1,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r1_lattice3(sK0,X1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u91,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,X1,sK3(sK0,X0,sK2)) | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,sK2) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u135,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,X1,sK3(sK0,X0,sK2)) | m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,sK2) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u54,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,sK1,sK2) | m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2) | ~r1_lattice3(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u61,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK3(sK0,X0,sK2)) | r1_lattice3(sK0,X0,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u93,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,X0,X1) | r1_orders_2(sK0,X1,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u153,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,X0,X1) | r1_orders_2(sK0,X1,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u72,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,u1_struct_0(sK0),X0) | r1_orders_2(sK0,X0,sK3(sK0,sK1,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u119,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,u1_struct_0(sK0),X0) | r1_orders_2(sK0,X0,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u171,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,u1_struct_0(sK0),X0) | r1_orders_2(sK0,X0,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u124,negated_conjecture,
% 0.21/0.51      ~l1_orders_2(X0) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | r1_orders_2(X0,X1,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | ~m1_subset_1(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(X0)) | ~r1_lattice3(X0,u1_struct_0(sK0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u104,negated_conjecture,
% 0.21/0.51      ~l1_orders_2(X1) | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r1_orders_2(X1,X2,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | ~m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(X1)) | ~r1_lattice3(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u94,negated_conjecture,
% 0.21/0.51      ~l1_orders_2(X0) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r1_orders_2(X0,X1,sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | ~m1_subset_1(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(X0)) | ~r1_lattice3(X0,u1_struct_0(sK0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u66,negated_conjecture,
% 0.21/0.51      ~l1_orders_2(X1) | r1_lattice3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r1_orders_2(X1,X2,sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))) | ~m1_subset_1(sK3(sK0,X0,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(X1)) | ~r1_lattice3(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u57,negated_conjecture,
% 0.21/0.51      ~l1_orders_2(X0) | r1_orders_2(X0,X1,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(X0)) | ~r1_lattice3(X0,u1_struct_0(sK0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattice3(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u49,negated_conjecture,
% 0.21/0.51      ~l1_orders_2(X0) | ~m1_subset_1(sK3(sK0,X2,sK2),u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,sK3(sK0,X2,sK2)) | r1_lattice3(sK0,X2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u36,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u86,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u120,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u63,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X1) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u88,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X1) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u56,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u46,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3(sK0,X0,sK2),X0) | r1_lattice3(sK0,X0,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,axiom,
% 0.21/0.51      ~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u42,axiom,
% 0.21/0.51      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,axiom,
% 0.21/0.51      ~r2_hidden(X4,X1) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u55,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u84,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u58,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2)) | r1_lattice3(sK0,sK1,sK2) | m1_subset_1(sK3(sK0,sK1,sK2),X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u59,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X3)) | r2_hidden(sK3(sK0,sK1,sK2),X3) | r1_lattice3(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u95,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u96,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X3)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r2_hidden(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X3) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u125,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u126,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X3)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | r2_hidden(sK3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X3) | r1_lattice3(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u47,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_lattice3(sK0,X0,sK2) | m1_subset_1(sK3(sK0,X0,sK2),X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u48,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | r2_hidden(sK3(sK0,X2,sK2),X3) | r1_lattice3(sK0,X2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u67,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | r1_lattice3(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X4)).
% 0.21/0.51  
% 0.21/0.51  cnf(u68,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X5,k1_zfmisc_1(X6)) | r1_lattice3(sK0,X5,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r2_hidden(sK3(sK0,X5,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X6) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u105,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | r1_lattice3(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X4)).
% 0.21/0.51  
% 0.21/0.51  cnf(u106,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X5,k1_zfmisc_1(X6)) | r1_lattice3(sK0,X5,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r2_hidden(sK3(sK0,X5,sK3(sK0,k4_waybel_0(sK0,sK1),sK2)),X6) | m1_subset_1(sK3(sK0,u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u44,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,X0,X1),X0) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u45,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.51  
% 0.21/0.51  % (6578)# SZS output end Saturation.
% 0.21/0.51  % (6578)------------------------------
% 0.21/0.51  % (6578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6578)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (6578)Memory used [KB]: 5500
% 0.21/0.51  % (6578)Time elapsed: 0.083 s
% 0.21/0.51  % (6578)------------------------------
% 0.21/0.51  % (6578)------------------------------
% 0.21/0.51  % (6568)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.51  % (6555)Success in time 0.155 s
%------------------------------------------------------------------------------
