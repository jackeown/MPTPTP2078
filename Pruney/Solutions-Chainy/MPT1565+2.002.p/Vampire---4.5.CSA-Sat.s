%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:15 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 (  78 expanded)
%              Number of leaves         :   78 (  78 expanded)
%              Depth                    :    0
%              Number of atoms          :  264 ( 264 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u295,axiom,(
    ! [X11,X13,X12] :
      ( v1_xboole_0(sK5(X11,X12,X13))
      | sP0(X11,X12,X13)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) )).

tff(u294,axiom,(
    ! [X11,X13,X12] :
      ( v1_xboole_0(sK6(X11,X12,X13))
      | sP2(X11,X12,X13)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) )).

tff(u293,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) )).

tff(u292,axiom,(
    ! [X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u291,axiom,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u290,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u289,axiom,(
    ! [X9,X8,X10] :
      ( r2_hidden(sK5(X8,X9,X10),u1_struct_0(X9))
      | sP0(X8,X9,X10)
      | v1_xboole_0(u1_struct_0(X9)) ) )).

tff(u288,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) )).

tff(u287,axiom,(
    ! [X9,X8,X10] :
      ( r2_hidden(sK6(X8,X9,X10),u1_struct_0(X9))
      | sP2(X8,X9,X10)
      | v1_xboole_0(u1_struct_0(X9)) ) )).

tff(u286,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u285,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u284,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u283,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u282,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u281,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u280,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u279,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK6(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) )).

tff(u278,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | sP2(X0,X1,X2) ) )).

tff(u277,axiom,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u276,negated_conjecture,(
    l1_orders_2(sK4) )).

tff(u275,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | sP2(X2,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u274,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP2(sK5(X4,X5,X6),X5,X7) ) )).

tff(u273,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X6,X7,sK5(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | sP0(X4,X5,u1_struct_0(X6))
      | sP2(sK5(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u272,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK6(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP2(sK6(X4,X5,X6),X5,X7) ) )).

tff(u271,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X6,X7,sK6(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | sP2(X4,X5,u1_struct_0(X6))
      | sP2(sK6(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u270,axiom,(
    ! [X3,X4] :
      ( ~ r1_lattice3(X3,X4,sK7(u1_struct_0(X3)))
      | sP2(sK7(u1_struct_0(X3)),X3,X4)
      | ~ l1_orders_2(X3)
      | v1_xboole_0(u1_struct_0(X3)) ) )).

tff(u269,axiom,(
    ! [X1,X0,X2] :
      ( r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ v1_xboole_0(X1) ) )).

tff(u268,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,X3,sK5(X1,X0,X2))
      | sP0(X1,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u267,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,X3,sK5(X1,X2,u1_struct_0(X0)))
      | sP0(X1,X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u266,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,X3,sK6(X1,X0,X2))
      | sP2(X1,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u265,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,X3,sK6(X1,X2,u1_struct_0(X0)))
      | sP2(X1,X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u264,axiom,(
    ! [X1,X0] :
      ( r1_lattice3(X0,X1,sK7(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ v1_xboole_0(X1) ) )).

tff(u263,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u262,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2))
      | sP2(X0,X1,X2) ) )).

tff(u261,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | sP0(X2,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u260,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u259,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X6,X7,sK5(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | sP0(X4,X5,u1_struct_0(X6))
      | sP0(sK5(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u258,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK6(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP0(sK6(X4,X5,X6),X5,X7) ) )).

tff(u257,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X6,X7,sK6(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | sP2(X4,X5,u1_struct_0(X6))
      | sP0(sK6(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u256,axiom,(
    ! [X3,X4] :
      ( ~ r2_lattice3(X3,X4,sK7(u1_struct_0(X3)))
      | sP0(sK7(u1_struct_0(X3)),X3,X4)
      | ~ l1_orders_2(X3)
      | v1_xboole_0(u1_struct_0(X3)) ) )).

tff(u255,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ v1_xboole_0(X1) ) )).

tff(u254,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_lattice3(X0,X3,sK5(X1,X0,X2))
      | sP0(X1,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u253,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_lattice3(X0,X3,sK5(X1,X2,u1_struct_0(X0)))
      | sP0(X1,X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u252,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_lattice3(X0,X3,sK6(X1,X0,X2))
      | sP2(X1,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u251,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_lattice3(X0,X3,sK6(X1,X2,u1_struct_0(X0)))
      | sP2(X1,X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u250,axiom,(
    ! [X1,X0] :
      ( r2_lattice3(X0,X1,sK7(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ v1_xboole_0(X1) ) )).

tff(u249,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP0(X0,X1,X2)
      | r2_lattice3(X1,X2,X0)
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u248,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u247,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u246,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | sP0(X0,X1,u1_struct_0(X2))
      | r2_lattice3(X2,X3,sK5(X0,X1,u1_struct_0(X2))) ) )).

tff(u245,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK6(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r2_lattice3(X1,X3,sK6(X0,X1,X2)) ) )).

tff(u244,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK6(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | sP2(X0,X1,u1_struct_0(X2))
      | r2_lattice3(X2,X3,sK6(X0,X1,u1_struct_0(X2))) ) )).

tff(u243,axiom,(
    ! [X3,X4] :
      ( ~ sP0(sK7(u1_struct_0(X3)),X3,X4)
      | r2_lattice3(X3,X4,sK7(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | v1_xboole_0(u1_struct_0(X3)) ) )).

tff(u242,axiom,(
    ! [X3,X5,X4] :
      ( sP0(X3,X4,X5)
      | ~ v1_xboole_0(X5) ) )).

tff(u241,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u240,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u239,axiom,(
    ! [X1,X0,X2] :
      ( sP1(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u238,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK5(X4,X5,X6))
      | sP0(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u237,axiom,(
    ! [X11,X13,X10,X12] :
      ( sP1(X13,X12,sK5(X10,X11,u1_struct_0(X12)))
      | sP0(X10,X11,u1_struct_0(X12))
      | ~ l1_orders_2(X12) ) )).

tff(u236,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK6(X4,X5,X6))
      | sP2(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u235,axiom,(
    ! [X11,X13,X10,X12] :
      ( sP1(X13,X12,sK6(X10,X11,u1_struct_0(X12)))
      | sP2(X10,X11,u1_struct_0(X12))
      | ~ l1_orders_2(X12) ) )).

tff(u234,axiom,(
    ! [X3,X4] :
      ( sP1(X3,X4,sK7(u1_struct_0(X4)))
      | ~ l1_orders_2(X4)
      | v1_xboole_0(u1_struct_0(X4)) ) )).

tff(u233,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP2(X0,X1,X2)
      | r1_lattice3(X1,X2,X0)
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u232,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u231,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u230,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK5(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | sP0(X0,X1,u1_struct_0(X2))
      | r1_lattice3(X2,X3,sK5(X0,X1,u1_struct_0(X2))) ) )).

tff(u229,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK6(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r1_lattice3(X1,X3,sK6(X0,X1,X2)) ) )).

tff(u228,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK6(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | sP2(X0,X1,u1_struct_0(X2))
      | r1_lattice3(X2,X3,sK6(X0,X1,u1_struct_0(X2))) ) )).

tff(u227,axiom,(
    ! [X3,X4] :
      ( ~ sP2(sK7(u1_struct_0(X3)),X3,X4)
      | r1_lattice3(X3,X4,sK7(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | v1_xboole_0(u1_struct_0(X3)) ) )).

tff(u226,axiom,(
    ! [X3,X5,X4] :
      ( sP2(X3,X4,X5)
      | ~ v1_xboole_0(X5) ) )).

tff(u225,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ sP2(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u224,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP2(X2,X1,X0) ) )).

tff(u223,axiom,(
    ! [X1,X0,X2] :
      ( sP3(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u222,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u221,axiom,(
    ! [X9,X7,X8,X6] :
      ( sP3(X9,X8,sK5(X6,X7,u1_struct_0(X8)))
      | sP0(X6,X7,u1_struct_0(X8))
      | ~ l1_orders_2(X8) ) )).

tff(u220,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK6(X0,X1,X2))
      | sP2(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u219,axiom,(
    ! [X9,X7,X8,X6] :
      ( sP3(X9,X8,sK6(X6,X7,u1_struct_0(X8)))
      | sP2(X6,X7,u1_struct_0(X8))
      | ~ l1_orders_2(X8) ) )).

tff(u218,axiom,(
    ! [X3,X4] :
      ( sP3(X3,X4,sK7(u1_struct_0(X4)))
      | ~ l1_orders_2(X4)
      | v1_xboole_0(u1_struct_0(X4)) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:28:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (26545)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.50  % (26545)Refutation not found, incomplete strategy% (26545)------------------------------
% 0.21/0.50  % (26545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26545)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26545)Memory used [KB]: 895
% 0.21/0.50  % (26545)Time elapsed: 0.068 s
% 0.21/0.50  % (26545)------------------------------
% 0.21/0.50  % (26545)------------------------------
% 0.21/0.51  % (26547)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.51  % (26553)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (26548)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (26555)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.51  % (26556)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.51  % (26555)Refutation not found, incomplete strategy% (26555)------------------------------
% 0.21/0.51  % (26555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26555)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26555)Memory used [KB]: 895
% 0.21/0.51  % (26555)Time elapsed: 0.070 s
% 0.21/0.51  % (26555)------------------------------
% 0.21/0.51  % (26555)------------------------------
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (26547)# SZS output start Saturation.
% 0.21/0.52  tff(u295,axiom,
% 0.21/0.52      (![X11, X13, X12] : ((v1_xboole_0(sK5(X11,X12,X13)) | sP0(X11,X12,X13) | ~v1_xboole_0(u1_struct_0(X12)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u294,axiom,
% 0.21/0.52      (![X11, X13, X12] : ((v1_xboole_0(sK6(X11,X12,X13)) | sP2(X11,X12,X13) | ~v1_xboole_0(u1_struct_0(X12)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u293,axiom,
% 0.21/0.52      (![X1, X0] : ((~r2_hidden(X1,X0) | m1_subset_1(X1,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u292,axiom,
% 0.21/0.52      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u291,axiom,
% 0.21/0.52      (![X0] : ((r2_hidden(sK7(X0),X0) | v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u290,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u289,axiom,
% 0.21/0.52      (![X9, X8, X10] : ((r2_hidden(sK5(X8,X9,X10),u1_struct_0(X9)) | sP0(X8,X9,X10) | v1_xboole_0(u1_struct_0(X9)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u288,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((r2_hidden(sK6(X0,X1,X2),X2) | sP2(X0,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u287,axiom,
% 0.21/0.52      (![X9, X8, X10] : ((r2_hidden(sK6(X8,X9,X10),u1_struct_0(X9)) | sP2(X8,X9,X10) | v1_xboole_0(u1_struct_0(X9)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u286,axiom,
% 0.21/0.52      (![X1, X0] : ((~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u285,axiom,
% 0.21/0.52      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u284,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u283,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u282,axiom,
% 0.21/0.52      (![X1, X0] : ((m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u281,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u280,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u279,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((m1_subset_1(sK6(X0,X1,X2),X2) | sP2(X0,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u278,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) | sP2(X0,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u277,axiom,
% 0.21/0.52      (![X0] : ((m1_subset_1(sK7(X0),X0) | v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u276,negated_conjecture,
% 0.21/0.52      l1_orders_2(sK4)).
% 0.21/0.52  
% 0.21/0.52  tff(u275,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | sP2(X2,X0,X1) | ~l1_orders_2(X0) | ~v1_xboole_0(X2) | ~v1_xboole_0(u1_struct_0(X0)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u274,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP2(sK5(X4,X5,X6),X5,X7))))).
% 0.21/0.52  
% 0.21/0.52  tff(u273,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((~r1_lattice3(X6,X7,sK5(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | sP0(X4,X5,u1_struct_0(X6)) | sP2(sK5(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.52  
% 0.21/0.52  tff(u272,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK6(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP2(sK6(X4,X5,X6),X5,X7))))).
% 0.21/0.52  
% 0.21/0.52  tff(u271,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((~r1_lattice3(X6,X7,sK6(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | sP2(X4,X5,u1_struct_0(X6)) | sP2(sK6(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.52  
% 0.21/0.52  tff(u270,axiom,
% 0.21/0.52      (![X3, X4] : ((~r1_lattice3(X3,X4,sK7(u1_struct_0(X3))) | sP2(sK7(u1_struct_0(X3)),X3,X4) | ~l1_orders_2(X3) | v1_xboole_0(u1_struct_0(X3)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u269,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X2) | ~v1_xboole_0(u1_struct_0(X0)) | ~v1_xboole_0(X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u268,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((r1_lattice3(X0,X3,sK5(X1,X0,X2)) | sP0(X1,X0,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u267,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((r1_lattice3(X0,X3,sK5(X1,X2,u1_struct_0(X0))) | sP0(X1,X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u266,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((r1_lattice3(X0,X3,sK6(X1,X0,X2)) | sP2(X1,X0,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u265,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((r1_lattice3(X0,X3,sK6(X1,X2,u1_struct_0(X0))) | sP2(X1,X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u264,axiom,
% 0.21/0.52      (![X1, X0] : ((r1_lattice3(X0,X1,sK7(u1_struct_0(X0))) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)) | ~v1_xboole_0(X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u263,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~r1_orders_2(X1,sK5(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u262,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK6(X0,X1,X2)) | sP2(X0,X1,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u261,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | sP0(X2,X0,X1) | ~l1_orders_2(X0) | ~v1_xboole_0(X2) | ~v1_xboole_0(u1_struct_0(X0)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u260,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.21/0.52  
% 0.21/0.52  tff(u259,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((~r2_lattice3(X6,X7,sK5(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | sP0(X4,X5,u1_struct_0(X6)) | sP0(sK5(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.52  
% 0.21/0.52  tff(u258,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK6(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP0(sK6(X4,X5,X6),X5,X7))))).
% 0.21/0.52  
% 0.21/0.52  tff(u257,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((~r2_lattice3(X6,X7,sK6(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | sP2(X4,X5,u1_struct_0(X6)) | sP0(sK6(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.52  
% 0.21/0.52  tff(u256,axiom,
% 0.21/0.52      (![X3, X4] : ((~r2_lattice3(X3,X4,sK7(u1_struct_0(X3))) | sP0(sK7(u1_struct_0(X3)),X3,X4) | ~l1_orders_2(X3) | v1_xboole_0(u1_struct_0(X3)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u255,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X2) | ~v1_xboole_0(u1_struct_0(X0)) | ~v1_xboole_0(X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u254,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((r2_lattice3(X0,X3,sK5(X1,X0,X2)) | sP0(X1,X0,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u253,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((r2_lattice3(X0,X3,sK5(X1,X2,u1_struct_0(X0))) | sP0(X1,X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u252,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((r2_lattice3(X0,X3,sK6(X1,X0,X2)) | sP2(X1,X0,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u251,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((r2_lattice3(X0,X3,sK6(X1,X2,u1_struct_0(X0))) | sP2(X1,X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u250,axiom,
% 0.21/0.52      (![X1, X0] : ((r2_lattice3(X0,X1,sK7(u1_struct_0(X0))) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)) | ~v1_xboole_0(X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u249,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~sP0(X0,X1,X2) | r2_lattice3(X1,X2,X0) | ~l1_orders_2(X1) | ~v1_xboole_0(X0) | ~v1_xboole_0(u1_struct_0(X1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u248,axiom,
% 0.21/0.52      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u247,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u246,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | sP0(X0,X1,u1_struct_0(X2)) | r2_lattice3(X2,X3,sK5(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u245,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((~sP0(sK6(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r2_lattice3(X1,X3,sK6(X0,X1,X2)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u244,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((~sP0(sK6(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | sP2(X0,X1,u1_struct_0(X2)) | r2_lattice3(X2,X3,sK6(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u243,axiom,
% 0.21/0.52      (![X3, X4] : ((~sP0(sK7(u1_struct_0(X3)),X3,X4) | r2_lattice3(X3,X4,sK7(u1_struct_0(X3))) | ~l1_orders_2(X3) | v1_xboole_0(u1_struct_0(X3)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u242,axiom,
% 0.21/0.52      (![X3, X5, X4] : ((sP0(X3,X4,X5) | ~v1_xboole_0(X5))))).
% 0.21/0.52  
% 0.21/0.52  tff(u241,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u240,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u239,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((sP1(X0,X1,X2) | ~l1_orders_2(X1) | ~v1_xboole_0(X2) | ~v1_xboole_0(u1_struct_0(X1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u238,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK5(X4,X5,X6)) | sP0(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.52  
% 0.21/0.52  tff(u237,axiom,
% 0.21/0.52      (![X11, X13, X10, X12] : ((sP1(X13,X12,sK5(X10,X11,u1_struct_0(X12))) | sP0(X10,X11,u1_struct_0(X12)) | ~l1_orders_2(X12))))).
% 0.21/0.52  
% 0.21/0.52  tff(u236,axiom,
% 0.21/0.52      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK6(X4,X5,X6)) | sP2(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.52  
% 0.21/0.52  tff(u235,axiom,
% 0.21/0.52      (![X11, X13, X10, X12] : ((sP1(X13,X12,sK6(X10,X11,u1_struct_0(X12))) | sP2(X10,X11,u1_struct_0(X12)) | ~l1_orders_2(X12))))).
% 0.21/0.52  
% 0.21/0.52  tff(u234,axiom,
% 0.21/0.52      (![X3, X4] : ((sP1(X3,X4,sK7(u1_struct_0(X4))) | ~l1_orders_2(X4) | v1_xboole_0(u1_struct_0(X4)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u233,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~sP2(X0,X1,X2) | r1_lattice3(X1,X2,X0) | ~l1_orders_2(X1) | ~v1_xboole_0(X0) | ~v1_xboole_0(u1_struct_0(X1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u232,axiom,
% 0.21/0.52      (![X1, X0, X2, X4] : ((~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.52  
% 0.21/0.52  tff(u231,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((~sP2(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u230,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((~sP2(sK5(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | sP0(X0,X1,u1_struct_0(X2)) | r1_lattice3(X2,X3,sK5(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u229,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((~sP2(sK6(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r1_lattice3(X1,X3,sK6(X0,X1,X2)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u228,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((~sP2(sK6(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | sP2(X0,X1,u1_struct_0(X2)) | r1_lattice3(X2,X3,sK6(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.52  
% 0.21/0.52  tff(u227,axiom,
% 0.21/0.52      (![X3, X4] : ((~sP2(sK7(u1_struct_0(X3)),X3,X4) | r1_lattice3(X3,X4,sK7(u1_struct_0(X3))) | ~l1_orders_2(X3) | v1_xboole_0(u1_struct_0(X3)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u226,axiom,
% 0.21/0.52      (![X3, X5, X4] : ((sP2(X3,X4,X5) | ~v1_xboole_0(X5))))).
% 0.21/0.52  
% 0.21/0.52  tff(u225,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.52  
% 0.21/0.52  tff(u224,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP2(X2,X1,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u223,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((sP3(X0,X1,X2) | ~l1_orders_2(X1) | ~v1_xboole_0(X2) | ~v1_xboole_0(u1_struct_0(X1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u222,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u221,axiom,
% 0.21/0.52      (![X9, X7, X8, X6] : ((sP3(X9,X8,sK5(X6,X7,u1_struct_0(X8))) | sP0(X6,X7,u1_struct_0(X8)) | ~l1_orders_2(X8))))).
% 0.21/0.52  
% 0.21/0.52  tff(u220,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK6(X0,X1,X2)) | sP2(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u219,axiom,
% 0.21/0.52      (![X9, X7, X8, X6] : ((sP3(X9,X8,sK6(X6,X7,u1_struct_0(X8))) | sP2(X6,X7,u1_struct_0(X8)) | ~l1_orders_2(X8))))).
% 0.21/0.52  
% 0.21/0.52  tff(u218,axiom,
% 0.21/0.52      (![X3, X4] : ((sP3(X3,X4,sK7(u1_struct_0(X4))) | ~l1_orders_2(X4) | v1_xboole_0(u1_struct_0(X4)))))).
% 0.21/0.52  
% 0.21/0.52  % (26547)# SZS output end Saturation.
% 0.21/0.52  % (26547)------------------------------
% 0.21/0.52  % (26547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26547)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (26547)Memory used [KB]: 5500
% 0.21/0.52  % (26547)Time elapsed: 0.063 s
% 0.21/0.52  % (26547)------------------------------
% 0.21/0.52  % (26547)------------------------------
% 0.21/0.52  % (26539)Success in time 0.149 s
%------------------------------------------------------------------------------
