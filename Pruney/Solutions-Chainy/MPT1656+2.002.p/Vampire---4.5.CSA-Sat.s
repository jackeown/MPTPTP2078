%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:09 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 (  87 expanded)
%              Number of leaves         :   87 (  87 expanded)
%              Depth                    :    0
%              Number of atoms          :  309 ( 309 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u329,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X2] :
        ( ~ r2_hidden(X2,k4_waybel_0(sK4,sK5))
        | ~ r2_hidden(X1,sK5)
        | ~ r1_orders_2(sK4,X1,sK6)
        | ~ m1_subset_1(X2,u1_struct_0(sK4))
        | r1_orders_2(sK4,X1,X2) ) )).

tff(u328,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | r1_orders_2(sK4,sK6,X0) ) )).

tff(u327,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u326,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) )).

tff(u325,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u324,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u323,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u322,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u321,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK7(X1,X2,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4))
        | ~ r1_orders_2(sK4,X0,sK6)
        | ~ r2_hidden(X0,sK5)
        | r1_orders_2(sK4,X0,sK7(X1,X2,k4_waybel_0(sK4,sK5)))
        | sP0(X1,X2,k4_waybel_0(sK4,sK5)) ) )).

tff(u320,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK7(X0,X1,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4))
        | r1_orders_2(sK4,sK6,sK7(X0,X1,k4_waybel_0(sK4,sK5)))
        | sP0(X0,X1,k4_waybel_0(sK4,sK5)) ) )).

tff(u319,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X5,X4] :
        ( ~ m1_subset_1(sK8(X4,X5,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4))
        | ~ r1_orders_2(sK4,X3,sK6)
        | ~ r2_hidden(X3,sK5)
        | r1_orders_2(sK4,X3,sK8(X4,X5,k4_waybel_0(sK4,sK5)))
        | sP2(X4,X5,k4_waybel_0(sK4,sK5)) ) )).

tff(u318,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2] :
        ( ~ m1_subset_1(sK8(X2,X3,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4))
        | r1_orders_2(sK4,sK6,sK8(X2,X3,k4_waybel_0(sK4,sK5)))
        | sP2(X2,X3,k4_waybel_0(sK4,sK5)) ) )).

tff(u317,negated_conjecture,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK4))
      | ~ r2_hidden(X0,sK5) ) )).

tff(u316,negated_conjecture,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) )).

tff(u315,negated_conjecture,(
    m1_subset_1(sK6,u1_struct_0(sK4)) )).

tff(u314,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u313,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | sP2(X0,X1,X2) ) )).

tff(u312,negated_conjecture,(
    ~ v2_struct_0(sK4) )).

tff(u311,negated_conjecture,(
    v3_orders_2(sK4) )).

tff(u310,negated_conjecture,(
    l1_orders_2(sK4) )).

tff(u309,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK7(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u308,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK8(X0,X1,X2))
      | sP2(X0,X1,X2) ) )).

tff(u307,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X5,X6] :
        ( ~ r1_orders_2(sK4,X6,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK4))
        | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X6)
        | ~ r1_orders_2(sK4,X5,sK6)
        | ~ m1_subset_1(X6,u1_struct_0(sK4)) ) )).

tff(u306,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X5,X6] :
        ( ~ r1_orders_2(sK4,X6,X5)
        | ~ r1_orders_2(sK4,X5,sK6)
        | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X6)
        | ~ r2_hidden(X5,sK5)
        | ~ m1_subset_1(X6,u1_struct_0(sK4)) ) )).

tff(u305,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X5,X4,X6] :
        ( ~ r1_orders_2(sK4,sK7(X4,sK4,X5),sK6)
        | sP0(X4,sK4,X5)
        | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X6)
        | ~ r1_orders_2(sK4,X6,sK7(X4,sK4,X5))
        | ~ m1_subset_1(X6,u1_struct_0(sK4)) ) )).

tff(u304,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X5,X4,X6] :
        ( ~ r1_orders_2(sK4,sK7(X4,sK4,X5),sK6)
        | sP0(X4,sK4,X5)
        | ~ r2_hidden(X6,k4_waybel_0(sK4,sK5))
        | ~ m1_subset_1(X6,u1_struct_0(sK4))
        | r1_orders_2(sK4,sK7(X4,sK4,X5),X6) ) )).

tff(u303,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X5,X4] :
        ( ~ r1_orders_2(sK4,sK7(sK7(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5),sK6)
        | ~ r2_hidden(sK7(sK7(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5),sK5)
        | sP0(X4,sK4,k4_waybel_0(sK4,sK5))
        | sP0(sK7(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5) ) )).

tff(u302,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X5,X4] :
        ( ~ r1_orders_2(sK4,sK7(sK8(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5),sK6)
        | ~ r2_hidden(sK7(sK8(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5),sK5)
        | sP2(X4,sK4,k4_waybel_0(sK4,sK5))
        | sP0(sK8(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5) ) )).

tff(u301,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X7,X8,X6] :
        ( ~ r1_orders_2(sK4,sK7(sK7(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8),sK6)
        | ~ r2_hidden(sK7(sK7(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8),sK5)
        | sP0(X6,X7,k4_waybel_0(sK4,sK5))
        | ~ r2_hidden(sK7(X6,X7,k4_waybel_0(sK4,sK5)),sK5)
        | sP0(sK7(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8) ) )).

tff(u300,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X7,X8,X6] :
        ( ~ r1_orders_2(sK4,sK7(sK8(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8),sK6)
        | ~ r2_hidden(sK7(sK8(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8),sK5)
        | sP2(X6,X7,k4_waybel_0(sK4,sK5))
        | ~ r2_hidden(sK8(X6,X7,k4_waybel_0(sK4,sK5)),sK5)
        | sP0(sK8(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8) ) )).

tff(u299,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X5,X4,X6] :
        ( ~ r1_orders_2(sK4,sK8(X4,sK4,X5),sK6)
        | sP2(X4,sK4,X5)
        | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X6)
        | ~ r1_orders_2(sK4,X6,sK8(X4,sK4,X5))
        | ~ m1_subset_1(X6,u1_struct_0(sK4)) ) )).

tff(u298,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X5,X4,X6] :
        ( ~ r1_orders_2(sK4,sK8(X4,sK4,X5),sK6)
        | sP2(X4,sK4,X5)
        | ~ r2_hidden(X6,k4_waybel_0(sK4,sK5))
        | ~ m1_subset_1(X6,u1_struct_0(sK4))
        | r1_orders_2(sK4,sK8(X4,sK4,X5),X6) ) )).

tff(u297,negated_conjecture,(
    r1_orders_2(sK4,sK6,sK6) )).

tff(u296,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( r1_orders_2(sK4,sK6,sK7(X0,sK4,k4_waybel_0(sK4,sK5)))
        | sP0(X0,sK4,k4_waybel_0(sK4,sK5)) ) )).

tff(u295,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X2] :
        ( r1_orders_2(sK4,sK6,sK7(X1,X2,k4_waybel_0(sK4,sK5)))
        | sP0(X1,X2,k4_waybel_0(sK4,sK5))
        | ~ r2_hidden(sK7(X1,X2,k4_waybel_0(sK4,sK5)),sK5) ) )).

tff(u294,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( r1_orders_2(sK4,sK6,sK8(X0,sK4,k4_waybel_0(sK4,sK5)))
        | sP2(X0,sK4,k4_waybel_0(sK4,sK5)) ) )).

tff(u293,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X2] :
        ( r1_orders_2(sK4,sK6,sK8(X1,X2,k4_waybel_0(sK4,sK5)))
        | sP2(X1,X2,k4_waybel_0(sK4,sK5))
        | ~ r2_hidden(sK8(X1,X2,k4_waybel_0(sK4,sK5)),sK5) ) )).

tff(u292,negated_conjecture,(
    ! [X0] :
      ( r1_orders_2(sK4,X0,X0)
      | ~ r2_hidden(X0,sK5) ) )).

tff(u291,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X0] :
        ( r1_orders_2(sK4,X0,sK7(X1,sK4,k4_waybel_0(sK4,sK5)))
        | ~ r2_hidden(X0,sK5)
        | ~ r1_orders_2(sK4,X0,sK6)
        | sP0(X1,sK4,k4_waybel_0(sK4,sK5)) ) )).

tff(u290,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2,X4] :
        ( r1_orders_2(sK4,X2,sK7(X3,X4,k4_waybel_0(sK4,sK5)))
        | ~ r2_hidden(X2,sK5)
        | ~ r1_orders_2(sK4,X2,sK6)
        | sP0(X3,X4,k4_waybel_0(sK4,sK5))
        | ~ r2_hidden(sK7(X3,X4,k4_waybel_0(sK4,sK5)),sK5) ) )).

tff(u289,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X0] :
        ( r1_orders_2(sK4,X0,sK8(X1,sK4,k4_waybel_0(sK4,sK5)))
        | ~ r2_hidden(X0,sK5)
        | ~ r1_orders_2(sK4,X0,sK6)
        | sP2(X1,sK4,k4_waybel_0(sK4,sK5)) ) )).

tff(u288,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2,X4] :
        ( r1_orders_2(sK4,X2,sK8(X3,X4,k4_waybel_0(sK4,sK5)))
        | ~ r2_hidden(X2,sK5)
        | ~ r1_orders_2(sK4,X2,sK6)
        | sP2(X3,X4,k4_waybel_0(sK4,sK5))
        | ~ r2_hidden(sK8(X3,X4,k4_waybel_0(sK4,sK5)),sK5) ) )).

tff(u287,axiom,(
    ! [X1,X3,X2] :
      ( r1_orders_2(X1,sK7(X2,X1,X3),sK7(X2,X1,X3))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | sP0(X2,X1,X3) ) )).

tff(u286,axiom,(
    ! [X5,X4,X6] :
      ( r1_orders_2(X4,sK8(X5,X4,X6),sK8(X5,X4,X6))
      | ~ l1_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | sP2(X5,X4,X6) ) )).

tff(u285,negated_conjecture,
    ( ~ ~ r1_lattice3(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,sK5,sK6) )).

tff(u284,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK4,X0,sK6)
      | sP2(sK6,sK4,X0) ) )).

tff(u283,negated_conjecture,(
    ! [X1,X2] :
      ( ~ r1_lattice3(sK4,X1,X2)
      | sP2(X2,sK4,X1)
      | ~ r2_hidden(X2,sK5) ) )).

tff(u282,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK7(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP2(sK7(X4,X5,X6),X5,X7) ) )).

tff(u281,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK8(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP2(sK8(X4,X5,X6),X5,X7) ) )).

tff(u280,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u279,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X0)
        | ~ r2_hidden(X0,sK5)
        | ~ r1_orders_2(sK4,X0,sK6) ) )).

tff(u278,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X0)
        | ~ r1_orders_2(sK4,X0,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) ) )).

tff(u277,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6) )).

tff(u276,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2] :
        ( r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK7(X2,sK4,X3))
        | ~ r1_orders_2(sK4,sK7(X2,sK4,X3),sK6)
        | sP0(X2,sK4,X3) ) )).

tff(u275,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2] :
        ( r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK8(X2,sK4,X3))
        | ~ r1_orders_2(sK4,sK8(X2,sK4,X3),sK6)
        | sP2(X2,sK4,X3) ) )).

tff(u274,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK4,X0,sK6)
      | sP0(sK6,sK4,X0) ) )).

tff(u273,negated_conjecture,(
    ! [X1,X2] :
      ( ~ r2_lattice3(sK4,X1,X2)
      | sP0(X2,sK4,X1)
      | ~ r2_hidden(X2,sK5) ) )).

tff(u272,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK7(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK7(X4,X5,X6),X5,X7) ) )).

tff(u271,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK8(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP0(sK8(X4,X5,X6),X5,X7) ) )).

tff(u270,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u269,negated_conjecture,(
    v4_orders_2(sK4) )).

tff(u268,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK6,sK4,X0)
      | r2_lattice3(sK4,X0,sK6) ) )).

tff(u267,negated_conjecture,(
    ! [X1,X2] :
      ( ~ sP0(X1,sK4,X2)
      | r2_lattice3(sK4,X2,X1)
      | ~ r2_hidden(X1,sK5) ) )).

tff(u266,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u265,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK7(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK7(X0,X1,X2)) ) )).

tff(u264,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK8(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r2_lattice3(X1,X3,sK8(X0,X1,X2)) ) )).

tff(u263,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u262,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u261,negated_conjecture,(
    ! [X0] : sP1(X0,sK4,sK6) )).

tff(u260,negated_conjecture,(
    ! [X3,X2] :
      ( sP1(X3,sK4,X2)
      | ~ r2_hidden(X2,sK5) ) )).

tff(u259,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK7(X4,X5,X6))
      | sP0(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u258,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK8(X4,X5,X6))
      | sP2(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u257,negated_conjecture,(
    ! [X0] :
      ( ~ sP2(sK6,sK4,X0)
      | r1_lattice3(sK4,X0,sK6) ) )).

tff(u256,negated_conjecture,(
    ! [X1,X2] :
      ( ~ sP2(X1,sK4,X2)
      | r1_lattice3(sK4,X2,X1)
      | ~ r2_hidden(X1,sK5) ) )).

tff(u255,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u254,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK7(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK7(X0,X1,X2)) ) )).

tff(u253,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK8(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r1_lattice3(X1,X3,sK8(X0,X1,X2)) ) )).

tff(u252,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( sP2(X0,sK4,k4_waybel_0(sK4,sK5))
        | ~ r1_orders_2(sK4,X0,sK6)
        | ~ r2_hidden(X0,sK5) ) )).

tff(u251,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | sP2(sK6,sK4,k4_waybel_0(sK4,sK5)) )).

tff(u250,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X2] :
        ( sP2(sK7(X1,sK4,X2),sK4,k4_waybel_0(sK4,sK5))
        | sP0(X1,sK4,X2)
        | ~ r1_orders_2(sK4,sK7(X1,sK4,X2),sK6) ) )).

tff(u249,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X4] :
        ( sP2(sK8(X3,sK4,X4),sK4,k4_waybel_0(sK4,sK5))
        | sP2(X3,sK4,X4)
        | ~ r1_orders_2(sK4,sK8(X3,sK4,X4),sK6) ) )).

tff(u248,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ sP2(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u247,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP2(X2,X1,X0) ) )).

tff(u246,negated_conjecture,(
    ! [X0] : sP3(X0,sK4,sK6) )).

tff(u245,negated_conjecture,(
    ! [X1,X0] :
      ( sP3(X1,sK4,X0)
      | ~ r2_hidden(X0,sK5) ) )).

tff(u244,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK7(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u243,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK8(X0,X1,X2))
      | sP2(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (13554)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.45  % (13567)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.45  % (13567)Refutation not found, incomplete strategy% (13567)------------------------------
% 0.21/0.45  % (13567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (13567)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (13567)Memory used [KB]: 895
% 0.21/0.45  % (13567)Time elapsed: 0.004 s
% 0.21/0.45  % (13567)------------------------------
% 0.21/0.45  % (13567)------------------------------
% 0.21/0.45  % (13559)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (13559)# SZS output start Saturation.
% 0.21/0.46  tff(u329,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X2] : ((~r2_hidden(X2,k4_waybel_0(sK4,sK5)) | ~r2_hidden(X1,sK5) | ~r1_orders_2(sK4,X1,sK6) | ~m1_subset_1(X2,u1_struct_0(sK4)) | r1_orders_2(sK4,X1,X2)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u328,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((~r2_hidden(X0,k4_waybel_0(sK4,sK5)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | r1_orders_2(sK4,sK6,X0)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u327,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((r2_hidden(sK7(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u326,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((r2_hidden(sK8(X0,X1,X2),X2) | sP2(X0,X1,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u325,axiom,
% 0.21/0.46      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u324,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u323,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u322,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.21/0.46  
% 0.21/0.46  tff(u321,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X0, X2] : ((~m1_subset_1(sK7(X1,X2,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4)) | ~r1_orders_2(sK4,X0,sK6) | ~r2_hidden(X0,sK5) | r1_orders_2(sK4,X0,sK7(X1,X2,k4_waybel_0(sK4,sK5))) | sP0(X1,X2,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u320,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X0] : ((~m1_subset_1(sK7(X0,X1,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4)) | r1_orders_2(sK4,sK6,sK7(X0,X1,k4_waybel_0(sK4,sK5))) | sP0(X0,X1,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u319,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X5, X4] : ((~m1_subset_1(sK8(X4,X5,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4)) | ~r1_orders_2(sK4,X3,sK6) | ~r2_hidden(X3,sK5) | r1_orders_2(sK4,X3,sK8(X4,X5,k4_waybel_0(sK4,sK5))) | sP2(X4,X5,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u318,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2] : ((~m1_subset_1(sK8(X2,X3,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4)) | r1_orders_2(sK4,sK6,sK8(X2,X3,k4_waybel_0(sK4,sK5))) | sP2(X2,X3,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u317,negated_conjecture,
% 0.21/0.46      (![X0] : ((m1_subset_1(X0,u1_struct_0(sK4)) | ~r2_hidden(X0,sK5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u316,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))).
% 0.21/0.46  
% 0.21/0.46  tff(u315,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK6,u1_struct_0(sK4))).
% 0.21/0.46  
% 0.21/0.46  tff(u314,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u313,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) | sP2(X0,X1,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u312,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK4)).
% 0.21/0.46  
% 0.21/0.46  tff(u311,negated_conjecture,
% 0.21/0.46      v3_orders_2(sK4)).
% 0.21/0.46  
% 0.21/0.46  tff(u310,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK4)).
% 0.21/0.46  
% 0.21/0.46  tff(u309,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~r1_orders_2(X1,sK7(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u308,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK8(X0,X1,X2)) | sP2(X0,X1,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u307,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X5, X6] : ((~r1_orders_2(sK4,X6,X5) | ~m1_subset_1(X5,u1_struct_0(sK4)) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X6) | ~r1_orders_2(sK4,X5,sK6) | ~m1_subset_1(X6,u1_struct_0(sK4))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u306,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X5, X6] : ((~r1_orders_2(sK4,X6,X5) | ~r1_orders_2(sK4,X5,sK6) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X6) | ~r2_hidden(X5,sK5) | ~m1_subset_1(X6,u1_struct_0(sK4))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u305,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X5, X4, X6] : ((~r1_orders_2(sK4,sK7(X4,sK4,X5),sK6) | sP0(X4,sK4,X5) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X6) | ~r1_orders_2(sK4,X6,sK7(X4,sK4,X5)) | ~m1_subset_1(X6,u1_struct_0(sK4))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u304,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X5, X4, X6] : ((~r1_orders_2(sK4,sK7(X4,sK4,X5),sK6) | sP0(X4,sK4,X5) | ~r2_hidden(X6,k4_waybel_0(sK4,sK5)) | ~m1_subset_1(X6,u1_struct_0(sK4)) | r1_orders_2(sK4,sK7(X4,sK4,X5),X6)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u303,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X5, X4] : ((~r1_orders_2(sK4,sK7(sK7(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5),sK6) | ~r2_hidden(sK7(sK7(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5),sK5) | sP0(X4,sK4,k4_waybel_0(sK4,sK5)) | sP0(sK7(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u302,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X5, X4] : ((~r1_orders_2(sK4,sK7(sK8(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5),sK6) | ~r2_hidden(sK7(sK8(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5),sK5) | sP2(X4,sK4,k4_waybel_0(sK4,sK5)) | sP0(sK8(X4,sK4,k4_waybel_0(sK4,sK5)),sK4,X5)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u301,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X7, X8, X6] : ((~r1_orders_2(sK4,sK7(sK7(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8),sK6) | ~r2_hidden(sK7(sK7(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8),sK5) | sP0(X6,X7,k4_waybel_0(sK4,sK5)) | ~r2_hidden(sK7(X6,X7,k4_waybel_0(sK4,sK5)),sK5) | sP0(sK7(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u300,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X7, X8, X6] : ((~r1_orders_2(sK4,sK7(sK8(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8),sK6) | ~r2_hidden(sK7(sK8(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8),sK5) | sP2(X6,X7,k4_waybel_0(sK4,sK5)) | ~r2_hidden(sK8(X6,X7,k4_waybel_0(sK4,sK5)),sK5) | sP0(sK8(X6,X7,k4_waybel_0(sK4,sK5)),sK4,X8)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u299,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X5, X4, X6] : ((~r1_orders_2(sK4,sK8(X4,sK4,X5),sK6) | sP2(X4,sK4,X5) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X6) | ~r1_orders_2(sK4,X6,sK8(X4,sK4,X5)) | ~m1_subset_1(X6,u1_struct_0(sK4))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u298,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X5, X4, X6] : ((~r1_orders_2(sK4,sK8(X4,sK4,X5),sK6) | sP2(X4,sK4,X5) | ~r2_hidden(X6,k4_waybel_0(sK4,sK5)) | ~m1_subset_1(X6,u1_struct_0(sK4)) | r1_orders_2(sK4,sK8(X4,sK4,X5),X6)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u297,negated_conjecture,
% 0.21/0.46      r1_orders_2(sK4,sK6,sK6)).
% 0.21/0.46  
% 0.21/0.46  tff(u296,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((r1_orders_2(sK4,sK6,sK7(X0,sK4,k4_waybel_0(sK4,sK5))) | sP0(X0,sK4,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u295,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X2] : ((r1_orders_2(sK4,sK6,sK7(X1,X2,k4_waybel_0(sK4,sK5))) | sP0(X1,X2,k4_waybel_0(sK4,sK5)) | ~r2_hidden(sK7(X1,X2,k4_waybel_0(sK4,sK5)),sK5)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u294,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((r1_orders_2(sK4,sK6,sK8(X0,sK4,k4_waybel_0(sK4,sK5))) | sP2(X0,sK4,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u293,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X2] : ((r1_orders_2(sK4,sK6,sK8(X1,X2,k4_waybel_0(sK4,sK5))) | sP2(X1,X2,k4_waybel_0(sK4,sK5)) | ~r2_hidden(sK8(X1,X2,k4_waybel_0(sK4,sK5)),sK5)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u292,negated_conjecture,
% 0.21/0.46      (![X0] : ((r1_orders_2(sK4,X0,X0) | ~r2_hidden(X0,sK5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u291,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X0] : ((r1_orders_2(sK4,X0,sK7(X1,sK4,k4_waybel_0(sK4,sK5))) | ~r2_hidden(X0,sK5) | ~r1_orders_2(sK4,X0,sK6) | sP0(X1,sK4,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u290,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2, X4] : ((r1_orders_2(sK4,X2,sK7(X3,X4,k4_waybel_0(sK4,sK5))) | ~r2_hidden(X2,sK5) | ~r1_orders_2(sK4,X2,sK6) | sP0(X3,X4,k4_waybel_0(sK4,sK5)) | ~r2_hidden(sK7(X3,X4,k4_waybel_0(sK4,sK5)),sK5)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u289,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X0] : ((r1_orders_2(sK4,X0,sK8(X1,sK4,k4_waybel_0(sK4,sK5))) | ~r2_hidden(X0,sK5) | ~r1_orders_2(sK4,X0,sK6) | sP2(X1,sK4,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u288,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2, X4] : ((r1_orders_2(sK4,X2,sK8(X3,X4,k4_waybel_0(sK4,sK5))) | ~r2_hidden(X2,sK5) | ~r1_orders_2(sK4,X2,sK6) | sP2(X3,X4,k4_waybel_0(sK4,sK5)) | ~r2_hidden(sK8(X3,X4,k4_waybel_0(sK4,sK5)),sK5)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u287,axiom,
% 0.21/0.46      (![X1, X3, X2] : ((r1_orders_2(X1,sK7(X2,X1,X3),sK7(X2,X1,X3)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | sP0(X2,X1,X3))))).
% 0.21/0.46  
% 0.21/0.46  tff(u286,axiom,
% 0.21/0.46      (![X5, X4, X6] : ((r1_orders_2(X4,sK8(X5,X4,X6),sK8(X5,X4,X6)) | ~l1_orders_2(X4) | ~v3_orders_2(X4) | v2_struct_0(X4) | sP2(X5,X4,X6))))).
% 0.21/0.46  
% 0.21/0.46  tff(u285,negated_conjecture,
% 0.21/0.46      ((~~r1_lattice3(sK4,sK5,sK6)) | ~r1_lattice3(sK4,sK5,sK6))).
% 0.21/0.46  
% 0.21/0.46  tff(u284,negated_conjecture,
% 0.21/0.46      (![X0] : ((~r1_lattice3(sK4,X0,sK6) | sP2(sK6,sK4,X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u283,negated_conjecture,
% 0.21/0.46      (![X1, X2] : ((~r1_lattice3(sK4,X1,X2) | sP2(X2,sK4,X1) | ~r2_hidden(X2,sK5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u282,axiom,
% 0.21/0.46      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK7(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP2(sK7(X4,X5,X6),X5,X7))))).
% 0.21/0.46  
% 0.21/0.46  tff(u281,axiom,
% 0.21/0.46      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK8(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP2(sK8(X4,X5,X6),X5,X7))))).
% 0.21/0.46  
% 0.21/0.46  tff(u280,axiom,
% 0.21/0.46      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u279,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X0) | ~r2_hidden(X0,sK5) | ~r1_orders_2(sK4,X0,sK6)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u278,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((r1_lattice3(sK4,k4_waybel_0(sK4,sK5),X0) | ~r1_orders_2(sK4,X0,sK6) | ~m1_subset_1(X0,u1_struct_0(sK4))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u277,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6))).
% 0.21/0.46  
% 0.21/0.46  tff(u276,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2] : ((r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK7(X2,sK4,X3)) | ~r1_orders_2(sK4,sK7(X2,sK4,X3),sK6) | sP0(X2,sK4,X3)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u275,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2] : ((r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK8(X2,sK4,X3)) | ~r1_orders_2(sK4,sK8(X2,sK4,X3),sK6) | sP2(X2,sK4,X3)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u274,negated_conjecture,
% 0.21/0.46      (![X0] : ((~r2_lattice3(sK4,X0,sK6) | sP0(sK6,sK4,X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u273,negated_conjecture,
% 0.21/0.46      (![X1, X2] : ((~r2_lattice3(sK4,X1,X2) | sP0(X2,sK4,X1) | ~r2_hidden(X2,sK5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u272,axiom,
% 0.21/0.46      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK7(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK7(X4,X5,X6),X5,X7))))).
% 0.21/0.46  
% 0.21/0.46  tff(u271,axiom,
% 0.21/0.46      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK8(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP0(sK8(X4,X5,X6),X5,X7))))).
% 0.21/0.46  
% 0.21/0.46  tff(u270,axiom,
% 0.21/0.46      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u269,negated_conjecture,
% 0.21/0.46      v4_orders_2(sK4)).
% 0.21/0.46  
% 0.21/0.46  tff(u268,negated_conjecture,
% 0.21/0.46      (![X0] : ((~sP0(sK6,sK4,X0) | r2_lattice3(sK4,X0,sK6))))).
% 0.21/0.46  
% 0.21/0.46  tff(u267,negated_conjecture,
% 0.21/0.46      (![X1, X2] : ((~sP0(X1,sK4,X2) | r2_lattice3(sK4,X2,X1) | ~r2_hidden(X1,sK5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u266,axiom,
% 0.21/0.46      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u265,axiom,
% 0.21/0.46      (![X1, X3, X0, X2] : ((~sP0(sK7(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK7(X0,X1,X2)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u264,axiom,
% 0.21/0.46      (![X1, X3, X0, X2] : ((~sP0(sK8(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r2_lattice3(X1,X3,sK8(X0,X1,X2)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u263,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u262,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u261,negated_conjecture,
% 0.21/0.46      (![X0] : (sP1(X0,sK4,sK6)))).
% 0.21/0.46  
% 0.21/0.46  tff(u260,negated_conjecture,
% 0.21/0.46      (![X3, X2] : ((sP1(X3,sK4,X2) | ~r2_hidden(X2,sK5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u259,axiom,
% 0.21/0.46      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK7(X4,X5,X6)) | sP0(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u258,axiom,
% 0.21/0.46      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK8(X4,X5,X6)) | sP2(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u257,negated_conjecture,
% 0.21/0.46      (![X0] : ((~sP2(sK6,sK4,X0) | r1_lattice3(sK4,X0,sK6))))).
% 0.21/0.46  
% 0.21/0.46  tff(u256,negated_conjecture,
% 0.21/0.46      (![X1, X2] : ((~sP2(X1,sK4,X2) | r1_lattice3(sK4,X2,X1) | ~r2_hidden(X1,sK5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u255,axiom,
% 0.21/0.46      (![X1, X0, X2, X4] : ((~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.46  
% 0.21/0.46  tff(u254,axiom,
% 0.21/0.46      (![X1, X3, X0, X2] : ((~sP2(sK7(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK7(X0,X1,X2)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u253,axiom,
% 0.21/0.46      (![X1, X3, X0, X2] : ((~sP2(sK8(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r1_lattice3(X1,X3,sK8(X0,X1,X2)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u252,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((sP2(X0,sK4,k4_waybel_0(sK4,sK5)) | ~r1_orders_2(sK4,X0,sK6) | ~r2_hidden(X0,sK5)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u251,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | sP2(sK6,sK4,k4_waybel_0(sK4,sK5)))).
% 0.21/0.46  
% 0.21/0.46  tff(u250,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X2] : ((sP2(sK7(X1,sK4,X2),sK4,k4_waybel_0(sK4,sK5)) | sP0(X1,sK4,X2) | ~r1_orders_2(sK4,sK7(X1,sK4,X2),sK6)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u249,negated_conjecture,
% 0.21/0.46      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X4] : ((sP2(sK8(X3,sK4,X4),sK4,k4_waybel_0(sK4,sK5)) | sP2(X3,sK4,X4) | ~r1_orders_2(sK4,sK8(X3,sK4,X4),sK6)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u248,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.46  
% 0.21/0.46  tff(u247,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP2(X2,X1,X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u246,negated_conjecture,
% 0.21/0.46      (![X0] : (sP3(X0,sK4,sK6)))).
% 0.21/0.46  
% 0.21/0.46  tff(u245,negated_conjecture,
% 0.21/0.46      (![X1, X0] : ((sP3(X1,sK4,X0) | ~r2_hidden(X0,sK5))))).
% 0.21/0.46  
% 0.21/0.46  tff(u244,axiom,
% 0.21/0.46      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK7(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.46  
% 0.21/0.46  tff(u243,axiom,
% 0.21/0.46      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK8(X0,X1,X2)) | sP2(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.46  
% 0.21/0.46  % (13559)# SZS output end Saturation.
% 0.21/0.46  % (13559)------------------------------
% 0.21/0.46  % (13559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (13559)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (13559)Memory used [KB]: 5500
% 0.21/0.46  % (13559)Time elapsed: 0.007 s
% 0.21/0.46  % (13559)------------------------------
% 0.21/0.46  % (13559)------------------------------
% 0.21/0.46  % (13551)Success in time 0.109 s
%------------------------------------------------------------------------------
