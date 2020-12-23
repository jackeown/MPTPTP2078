%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:09 EST 2020

% Result     : CounterSatisfiable 27.79s
% Output     : Model 27.79s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :  379 ( 379 expanded)
%              Number of equality atoms :  367 ( 367 expanded)
%              Maximal formula depth    :   69 (  18 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Positive definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0_2,X1_2] :
      ( equality_sorted(X0_0,X0_2,X1_2)
    <=> ( ( X0_0 = $o
          & X1_2 = X0_2 )
        | ( X0_0 = $i
          & X0 != u1_struct_0(X0)
          & X0 != sK8
          & ( X0 != sK8
            | X1 != u1_struct_0(X1) )
          & ( X0 != sK8
            | X1 != arAF0_sK1_0_1(sK8) )
          & ( X0 != sK8
            | X1 != arAF0_sK1_0_1(arAF0_sK2_0) )
          & X0 != u1_struct_0(sK6)
          & ( X0 != u1_struct_0(sK6)
            | X1 != sK8 )
          & ( X0 != u1_struct_0(sK6)
            | X1 != arAF0_sK2_0 )
          & ( X0 != u1_struct_0(sK6)
            | X1 != arAF0_sK3_0 )
          & ( X0 != u1_struct_0(X2)
            | X1 != sK8 )
          & ( X0 != u1_struct_0(X2)
            | X1 != arAF0_sK2_0 )
          & ( X0 != u1_struct_0(X2)
            | X1 != arAF0_sK3_0 )
          & ( X0 != u1_struct_0(X2)
            | X1 != arAF0_sK1_0_1(sK8) )
          & ( X0 != u1_struct_0(X2)
            | X1 != arAF0_sK1_0_1(arAF0_sK2_0) )
          & ( X0 != arAF0_k1_yellow_0_0
            | X1 != u1_struct_0(X0) )
          & ( X0 != arAF0_k1_yellow_0_0
            | X1 != sK8 )
          & ( X0 != arAF0_k1_yellow_0_0
            | X1 != u1_struct_0(sK6) )
          & ( X0 != arAF0_k1_yellow_0_0
            | X1 != arAF0_sK2_0 )
          & ( X0 != arAF0_k1_yellow_0_0
            | X1 != arAF0_sK1_0_1(arAF0_sK2_0) )
          & X0 != arAF0_sK2_0
          & ( X0 != arAF0_sK2_0
            | X1 != u1_struct_0(X1) )
          & ( X0 != arAF0_sK2_0
            | X1 != u1_struct_0(X0) )
          & ( X0 != arAF0_sK2_0
            | X1 != u1_struct_0(sK6) )
          & ( X0 != arAF0_sK2_0
            | X1 != arAF0_k1_yellow_0_0 )
          & ( X0 != arAF0_sK2_0
            | X1 != arAF0_sK1_0_1(sK8) )
          & ( X0 != arAF0_sK2_0
            | X1 != arAF0_sK1_0_1(arAF0_sK2_0) )
          & ( X0 != arAF0_sK2_0
            | X1 != sK4(X0,sK8) )
          & X0 != arAF0_sK3_0
          & ( X0 != arAF0_sK3_0
            | X1 != u1_struct_0(X1) )
          & ( X0 != arAF0_sK3_0
            | X1 != arAF0_sK1_0_1(sK8) )
          & ( X0 != arAF0_sK3_0
            | X1 != arAF0_sK1_0_1(arAF0_sK2_0) )
          & X0 != arAF0_sK1_0_1(sK8)
          & ( X0 != arAF0_sK1_0_1(sK8)
            | X1 != u1_struct_0(X0) )
          & ( X0 != arAF0_sK1_0_1(sK8)
            | X1 != sK8 )
          & ( X0 != arAF0_sK1_0_1(sK8)
            | X1 != arAF0_k1_yellow_0_0 )
          & ( X0 != arAF0_sK1_0_1(sK8)
            | X1 != arAF0_sK2_0 )
          & ( X0 != arAF0_sK1_0_1(sK8)
            | X1 != arAF0_sK3_0 )
          & ( X0 != arAF0_sK1_0_1(sK8)
            | X1 != arAF0_sK1_0_1(arAF0_sK2_0) )
          & ( X0 != arAF0_sK1_0_1(sK8)
            | X1 != sK4(X0,sK8) )
          & ( X0 != arAF0_sK1_0_1(sK8)
            | X1 != sK4(X1,sK8) )
          & X0 != arAF0_sK1_0_1(arAF0_sK2_0)
          & ( X0 != arAF0_sK1_0_1(arAF0_sK2_0)
            | X1 != u1_struct_0(X1) )
          & ( X0 != arAF0_sK1_0_1(arAF0_sK2_0)
            | X1 != u1_struct_0(X0) )
          & ( X0 != arAF0_sK1_0_1(arAF0_sK2_0)
            | X1 != sK8 )
          & ( X0 != arAF0_sK1_0_1(arAF0_sK2_0)
            | X1 != arAF0_sK2_0 )
          & ( X0 != arAF0_sK1_0_1(arAF0_sK2_0)
            | X1 != arAF0_sK3_0 )
          & ( X0 != sK4(sK6,sK8)
            | X1 != u1_struct_0(X0) )
          & ( X0 != sK4(sK6,sK8)
            | X1 != sK8 )
          & ( X0 != sK4(sK6,sK8)
            | X1 != arAF0_sK2_0 )
          & ( X0 != sK4(sK6,sK8)
            | X1 != arAF0_sK1_0_1(sK8) )
          & ( X0 != sK4(sK6,sK8)
            | X1 != arAF0_sK1_0_1(arAF0_sK2_0) )
          & X0 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0))
          & ( X0 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0))
            | X1 != arAF0_sK1_0_1(sK8) )
          & ( X0 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0))
            | X1 != arAF0_sK1_0_1(arAF0_sK2_0) )
          & X1 != u1_struct_0(X1)
          & X1 != sK8
          & X1 != arAF0_sK2_0
          & X1 != arAF0_sK3_0
          & X1 != arAF0_sK1_0_1(sK8)
          & X1 != arAF0_sK1_0_1(arAF0_sK2_0)
          & X1 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = u1_struct_0(sK6)
            & X1 = u1_struct_0(X2) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(sK6) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(X3) )
        | ( X0_0 = $i
          & X0 = arAF0_k1_yellow_0_0
          & X1 != u1_struct_0(X1)
          & X1 != sK8
          & X1 != u1_struct_0(sK6)
          & X1 != arAF0_sK2_0
          & X1 != arAF0_sK3_0
          & X1 != arAF0_sK1_0_1(sK8)
          & X1 != arAF0_sK1_0_1(arAF0_sK2_0)
          & X1 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
        | ( X0_0 = $i
          & X0 = arAF0_k1_yellow_0_0
          & X1 = arAF0_sK1_0_1(sK8) )
        | ( X0_0 = $i
          & X0 = arAF0_k1_yellow_0_0
          & X1 = arAF0_sK1_0_1(arAF0_sK2_0) )
        | ( X0_0 = $i
          & X0 = arAF0_sK5_0
          & X1 = arAF0_sK1_0_1(sK8) )
        | ( X0_0 = $i
          & X0 = arAF0_sK1_0_1(sK8)
          & X1 != u1_struct_0(X1)
          & X1 != sK8
          & X1 != arAF0_sK2_0
          & X1 != arAF0_sK3_0
          & X1 != arAF0_sK5_0
          & X1 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
        | ( X0_0 = $i
          & X0 = arAF0_sK1_0_1(sK8)
          & X1 = arAF0_k1_yellow_0_0 )
        | ( X0_0 = $i
          & X0 = arAF0_sK1_0_1(sK8)
          & X1 = arAF0_sK5_0 )
        | ( X0_0 = $i
          & X0 = arAF0_sK1_0_1(sK8)
          & X1 = arAF0_sK1_0_1(arAF0_sK2_0) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = arAF0_sK1_0_1(sK8)
            & X1 = sK4(X2,sK8) )
        | ( X0_0 = $i
          & X0 = arAF0_sK1_0_1(arAF0_sK2_0)
          & X1 != u1_struct_0(X1)
          & X1 != sK8
          & X1 != arAF0_k1_yellow_0_0
          & X1 != arAF0_sK2_0
          & X1 != arAF0_sK3_0
          & X1 != arAF0_sK5_0
          & X1 != arAF0_sK1_0_1(sK8)
          & X1 != arAF0_sK1_0_1(arAF0_sK2_0)
          & X1 != sK4(sK6,sK8)
          & X1 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
        | ( X0_0 = $i
          & X0 = arAF0_sK1_0_1(arAF0_sK2_0)
          & X1 = arAF0_k1_yellow_0_0 )
        | ( X0_0 = $i
          & X0 = arAF0_sK1_0_1(arAF0_sK2_0)
          & X1 = arAF0_sK5_0 )
        | ( X0_0 = $i
          & X0 = arAF0_sK1_0_1(arAF0_sK2_0)
          & X1 = arAF0_sK1_0_1(sK8) )
        | ( X0_0 = $i
          & X0 = arAF0_sK1_0_1(arAF0_sK2_0)
          & X1 = sK4(sK6,sK8) )
        | ( X0_0 = $i
          & X0 = sK4(sK6,sK8)
          & X1 != u1_struct_0(X1)
          & X1 != sK8
          & X1 != arAF0_sK2_0
          & X1 != arAF0_sK3_0
          & X1 != arAF0_sK1_0_1(sK8)
          & X1 != arAF0_sK1_0_1(arAF0_sK2_0)
          & X1 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
        | ( X0_0 = $i
          & X0 = sK4(sK6,sK8)
          & X1 = arAF0_sK1_0_1(sK8) )
        | ( X0_0 = $i
          & X0 = sK4(sK6,sK8)
          & X1 = arAF0_sK1_0_1(arAF0_sK2_0) )
        | ( X0_0 = $i
          & X1 = X0 )
        | ( X0_0 = $i
          & X1 = arAF0_sK1_0_1(sK8)
          & X0 != u1_struct_0(X0)
          & X0 != sK8
          & X0 != arAF0_sK2_0
          & X0 != arAF0_sK3_0
          & X0 != arAF0_sK5_0
          & X0 != arAF0_sK1_0_1(sK8)
          & X0 != arAF0_sK1_0_1(arAF0_sK2_0)
          & X0 != sK4(sK6,sK8)
          & X0 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
        | ( X0_0 = $i
          & X1 = arAF0_sK1_0_1(arAF0_sK2_0)
          & X0 != u1_struct_0(X0)
          & X0 != sK8
          & X0 != arAF0_sK2_0
          & X0 != arAF0_sK3_0
          & X0 != arAF0_sK1_0_1(sK8)
          & X0 != sK4(sK6,sK8)
          & X0 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) ) ) ) )).

%------ Negative definition of sP0 
fof(lit_def_001,axiom,(
    ! [X0,X1,X2] :
      ( ~ sP0(X0,X1,X2)
    <=> ( ( X0 = sK8
          & X1 = sK6
          & X2 = sK8 )
        | ( X0 = sK8
          & X2 = sK8 )
        | ( X0 = u1_struct_0(sK6)
          & X1 = sK6
          & X2 = sK8 )
        | ( X0 = arAF0_sK2_0
          & X1 = sK6
          & X2 = sK8 )
        | ( X0 = arAF0_sK2_0
          & X2 = sK8 )
        | ( X0 = arAF0_sK3_0
          & X1 = sK6
          & X2 = sK8 )
        | ( X0 = arAF0_sK3_0
          & X2 = sK8 )
        | ? [X3] :
            ( X0 = u1_struct_0(X3)
            & X1 = sK6
            & X2 = sK8 )
        | ? [X3] :
            ( X0 = u1_struct_0(X3)
            & X2 = sK8 )
        | ( X0 = arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0))
          & X1 = sK6
          & X2 = sK8 )
        | ( X0 = arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0))
          & X2 = sK8 ) ) ) )).

%------ Negative definition of r1_orders_2 
fof(lit_def_002,axiom,(
    ! [X0,X1,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
    <=> ( ( X0 = sK6
          & X1 = sK8 )
        | ( X0 = sK6
          & X1 = sK8
          & X2 = arAF0_sK5_0 )
        | ( X0 = sK6
          & X1 = arAF0_k1_yellow_0_0
          & X2 = arAF0_sK2_0 )
        | ( X0 = sK6
          & X1 = arAF0_k1_yellow_0_0
          & X2 = arAF0_sK3_0 )
        | ( X0 = sK6
          & X1 = arAF0_sK3_0 )
        | ( X0 = sK6
          & X1 = arAF0_sK3_0
          & X2 = arAF0_sK5_0 )
        | ( X0 = sK6
          & X1 = sK4(sK6,sK8)
          & X2 = arAF0_sK2_0 )
        | ( X0 = sK6
          & X1 = sK4(sK6,sK8)
          & X2 = arAF0_sK3_0 )
        | ? [X3] :
            ( X0 = sK6
            & X1 = u1_struct_0(X3) )
        | X1 = sK8
        | ( X1 = sK8
          & X2 = arAF0_sK5_0 )
        | X1 = arAF0_sK3_0
        | ( X1 = arAF0_sK3_0
          & X2 = arAF0_sK5_0 )
        | ? [X3] : X1 = u1_struct_0(X3)
        | X2 = arAF0_sK2_0
        | X2 = arAF0_sK3_0 ) ) )).

%------ Positive definition of r2_lattice3 
fof(lit_def_003,axiom,(
    ! [X0,X1,X2] :
      ( r2_lattice3(X0,X1,X2)
    <=> ( ( X0 = sK6
          & X1 = sK8
          & X2 != sK8
          & X2 != arAF0_sK1_0_1(sK8)
          & X2 != arAF0_sK1_0_1(arAF0_sK2_0)
          & X2 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
        | ( X0 = sK6
          & X1 = sK8
          & X2 = arAF0_k1_yellow_0_0 )
        | ( X0 = sK6
          & X1 = sK8
          & X2 = arAF0_sK2_0 )
        | ( X0 = sK6
          & X1 = sK8
          & X2 = arAF0_sK5_0 )
        | ( X0 = sK6
          & X1 = sK8
          & X2 = arAF0_sK1_0_1(sK8) )
        | ( X0 = sK6
          & X1 = sK8
          & X2 = arAF0_sK1_0_1(arAF0_sK2_0) )
        | ( X0 = sK6
          & X1 = sK8
          & X2 = sK4(sK6,sK8) )
        | ? [X3] :
            ( X0 = sK6
            & X1 = sK8
            & X2 = arAF0_sK1_0_1(u1_struct_0(X3)) )
        | ( X0 = sK6
          & X1 = sK8
          & X2 = arAF0_sK1_0_1(arAF0_sK3_0) )
        | ( X0 = sK6
          & X1 = sK8
          & X2 = arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0))) )
        | ( X1 = sK8
          & ( X0 != sK6
            | X2 != sK8 )
          & ( X0 != sK6
            | X2 != arAF0_sK1_0_1(arAF0_sK2_0) )
          & ( X0 != sK6
            | X2 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
          & X2 != sK8
          & X2 != arAF0_sK1_0_1(sK8)
          & X2 != arAF0_sK1_0_1(arAF0_sK2_0)
          & X2 != arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
        | ( X1 = sK8
          & X2 = arAF0_k1_yellow_0_0 )
        | ( X1 = sK8
          & X2 = arAF0_sK2_0 )
        | ( X1 = sK8
          & X2 = arAF0_sK5_0 )
        | ( X1 = sK8
          & X2 = arAF0_sK1_0_1(sK8) )
        | ( X1 = sK8
          & X2 = arAF0_sK1_0_1(arAF0_sK2_0) )
        | ( X1 = sK8
          & X2 = sK4(sK6,sK8) )
        | ( X1 = sK8
          & X2 = sK4(X0,sK8) )
        | ? [X3] :
            ( X1 = sK8
            & X2 = arAF0_sK1_0_1(u1_struct_0(X3)) )
        | ( X1 = sK8
          & X2 = arAF0_sK1_0_1(arAF0_sK3_0) )
        | ( X1 = sK8
          & X2 = arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0))) )
        | X2 = arAF0_sK2_0 ) ) )).

%------ Negative definition of m1_subset_1 
fof(lit_def_004,axiom,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
    <=> ( ( X0 = u1_struct_0(sK6)
          & X1 = u1_struct_0(sK6) )
        | ? [X2] :
            ( X0 = u1_struct_0(sK6)
            & X1 = u1_struct_0(X2) )
        | ? [X2] : X0 = u1_struct_0(X2)
        | ? [X2] :
            ( X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(sK6) )
        | ? [X2,X3] :
            ( X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(X3) )
        | X0 = arAF0_sK2_0
        | ( X0 = arAF0_sK2_0
          & X1 = u1_struct_0(sK6) )
        | ? [X2] :
            ( X0 = arAF0_sK2_0
            & X1 = u1_struct_0(X2) )
        | X0 = arAF0_sK3_0
        | ( X0 = arAF0_sK3_0
          & X1 = u1_struct_0(sK6) )
        | ? [X2] :
            ( X0 = arAF0_sK3_0
            & X1 = u1_struct_0(X2) ) ) ) )).

%------ Positive definition of r1_yellow_0 
fof(lit_def_005,axiom,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
    <=> ( ( X0 = sK6
          & X1 = sK8 )
        | X1 = sK8 ) ) )).

%------ Positive definition of l1_orders_2 
fof(lit_def_006,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
    <=> $true ) )).

%------ Positive definition of r2_hidden 
fof(lit_def_007,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
    <=> $false ) )).

%------ Positive definition of v1_finset_1 
fof(lit_def_008,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
    <=> $false ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:56:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.79/3.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.79/3.99  
% 27.79/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.79/3.99  
% 27.79/3.99  ------  iProver source info
% 27.79/3.99  
% 27.79/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.79/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.79/3.99  git: non_committed_changes: false
% 27.79/3.99  git: last_make_outside_of_git: false
% 27.79/3.99  
% 27.79/3.99  ------ 
% 27.79/3.99  ------ Parsing...
% 27.79/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 3 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  ------ Proving...
% 27.79/3.99  ------ Problem Properties 
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  clauses                                 24
% 27.79/3.99  conjectures                             5
% 27.79/3.99  EPR                                     3
% 27.79/3.99  Horn                                    14
% 27.79/3.99  unary                                   3
% 27.79/3.99  binary                                  5
% 27.79/3.99  lits                                    92
% 27.79/3.99  lits eq                                 7
% 27.79/3.99  fd_pure                                 0
% 27.79/3.99  fd_pseudo                               0
% 27.79/3.99  fd_cond                                 0
% 27.79/3.99  fd_pseudo_cond                          6
% 27.79/3.99  AC symbols                              0
% 27.79/3.99  
% 27.79/3.99  ------ Input Options Time Limit: Unbounded
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing...
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 27.79/3.99  Current options:
% 27.79/3.99  ------ 
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing...
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  % SZS status CounterSatisfiable for theBenchmark.p
% 27.79/3.99  
% 27.79/3.99  ------ Building Model...Done
% 27.79/3.99  
% 27.79/3.99  %------ The model is defined over ground terms (initial term algebra).
% 27.79/3.99  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 27.79/3.99  %------ where \phi is a formula over the term algebra.
% 27.79/3.99  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 27.79/3.99  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 27.79/3.99  %------ See help for --sat_out_model for different model outputs.
% 27.79/3.99  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 27.79/3.99  %------ where the first argument stands for the sort ($i in the unsorted case)
% 27.79/3.99  % SZS output start Model for theBenchmark.p
% 27.79/3.99  
% 27.79/3.99  %------ Positive definition of equality_sorted 
% 27.79/3.99  fof(lit_def,axiom,
% 27.79/3.99      (! [X0_0,X0_2,X1_2] : 
% 27.79/3.99        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 27.79/3.99             (
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$o & X1_2=X0_2 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(X0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK8 | X1!=u1_struct_0(X1) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK8 | X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK8 | X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(sK6) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(sK6) | X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(sK6) | X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(sK6) | X1!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(X2) | X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(X2) | X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(X2) | X1!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(X2) | X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(X2) | X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_k1_yellow_0_0 | X1!=u1_struct_0(X0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_k1_yellow_0_0 | X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_k1_yellow_0_0 | X1!=u1_struct_0(sK6) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_k1_yellow_0_0 | X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_k1_yellow_0_0 | X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 | X1!=u1_struct_0(X1) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 | X1!=u1_struct_0(X0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 | X1!=u1_struct_0(sK6) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 | X1!=arAF0_k1_yellow_0_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 | X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 | X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 | X1!=sK4(X0,sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK3_0 | X1!=u1_struct_0(X1) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK3_0 | X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK3_0 | X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) | X1!=u1_struct_0(X0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) | X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) | X1!=arAF0_k1_yellow_0_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) | X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) | X1!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) | X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) | X1!=sK4(X0,sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) | X1!=sK4(X1,sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK2_0) | X1!=u1_struct_0(X1) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK2_0) | X1!=u1_struct_0(X0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK2_0) | X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK2_0) | X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK2_0) | X1!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK4(sK6,sK8) | X1!=u1_struct_0(X0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK4(sK6,sK8) | X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK4(sK6,sK8) | X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK4(sK6,sK8) | X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK4(sK6,sK8) | X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) | X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) | X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=u1_struct_0(X1) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=u1_struct_0(sK6) & X1=u1_struct_0(X2) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=u1_struct_0(X2) & X1=u1_struct_0(sK6) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2,X3] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=u1_struct_0(X2) & X1=u1_struct_0(X3) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_k1_yellow_0_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=u1_struct_0(X1) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=u1_struct_0(sK6) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_k1_yellow_0_0 & X1=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_k1_yellow_0_0 & X1=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK5_0 & X1=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=u1_struct_0(X1) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK5_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(sK8) & X1=arAF0_k1_yellow_0_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(sK8) & X1=arAF0_sK5_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(sK8) & X1=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(sK8) & X1=sK4(X2,sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=u1_struct_0(X1) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_k1_yellow_0_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK5_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=sK4(sK6,sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(arAF0_sK2_0) & X1=arAF0_k1_yellow_0_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(arAF0_sK2_0) & X1=arAF0_sK5_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(arAF0_sK2_0) & X1=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=arAF0_sK1_0_1(arAF0_sK2_0) & X1=sK4(sK6,sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=sK4(sK6,sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=u1_struct_0(X1) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X1!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=sK4(sK6,sK8) & X1=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X0=sK4(sK6,sK8) & X1=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X1=X0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X1=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(X0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK5_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK4(sK6,sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0_0=$i & X1=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=u1_struct_0(X0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK2_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK3_0 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK4(sK6,sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99             )
% 27.79/3.99        )
% 27.79/3.99      )
% 27.79/3.99     ).
% 27.79/3.99  
% 27.79/3.99  %------ Negative definition of sP0 
% 27.79/3.99  fof(lit_def,axiom,
% 27.79/3.99      (! [X0,X1,X2] : 
% 27.79/3.99        ( ~(sP0(X0,X1,X2)) <=>
% 27.79/3.99             (
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK8 & X1=sK6 & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK8 & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=u1_struct_0(sK6) & X1=sK6 & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK2_0 & X1=sK6 & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK2_0 & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK3_0 & X1=sK6 & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK3_0 & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X3] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=u1_struct_0(X3) & X1=sK6 & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X3] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=u1_struct_0(X3) & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) & X1=sK6 & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) & X2=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99             )
% 27.79/3.99        )
% 27.79/3.99      )
% 27.79/3.99     ).
% 27.79/3.99  
% 27.79/3.99  %------ Negative definition of r1_orders_2 
% 27.79/3.99  fof(lit_def,axiom,
% 27.79/3.99      (! [X0,X1,X2] : 
% 27.79/3.99        ( ~(r1_orders_2(X0,X1,X2)) <=>
% 27.79/3.99             (
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=arAF0_sK5_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=arAF0_k1_yellow_0_0 & X2=arAF0_sK2_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=arAF0_k1_yellow_0_0 & X2=arAF0_sK3_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=arAF0_sK3_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=arAF0_sK3_0 & X2=arAF0_sK5_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK4(sK6,sK8) & X2=arAF0_sK2_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK4(sK6,sK8) & X2=arAF0_sK3_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X3] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=u1_struct_0(X3) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=arAF0_sK5_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=arAF0_sK3_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=arAF0_sK3_0 & X2=arAF0_sK5_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X3] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=u1_struct_0(X3) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X2=arAF0_sK2_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X2=arAF0_sK3_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99             )
% 27.79/3.99        )
% 27.79/3.99      )
% 27.79/3.99     ).
% 27.79/3.99  
% 27.79/3.99  %------ Positive definition of r2_lattice3 
% 27.79/3.99  fof(lit_def,axiom,
% 27.79/3.99      (! [X0,X1,X2] : 
% 27.79/3.99        ( r2_lattice3(X0,X1,X2) <=>
% 27.79/3.99             (
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X2!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X2!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X2!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X2!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=arAF0_k1_yellow_0_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=arAF0_sK2_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=arAF0_sK5_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=sK4(sK6,sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X3] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=arAF0_sK1_0_1(u1_struct_0(X3)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=arAF0_sK1_0_1(arAF0_sK3_0) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 & X2=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0))) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK6 | X2!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK6 | X2!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X0!=sK6 | X2!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X2!=sK8 )
% 27.79/3.99                 &
% 27.79/3.99                  ( X2!=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X2!=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                 &
% 27.79/3.99                  ( X2!=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=arAF0_k1_yellow_0_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=arAF0_sK2_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=arAF0_sK5_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=arAF0_sK1_0_1(sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=arAF0_sK1_0_1(arAF0_sK2_0) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=sK4(sK6,sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=sK4(X0,sK8) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X3] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=arAF0_sK1_0_1(u1_struct_0(X3)) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=arAF0_sK1_0_1(arAF0_sK3_0) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 & X2=arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK1_0_1(arAF0_sK2_0))) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X2=arAF0_sK2_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99             )
% 27.79/3.99        )
% 27.79/3.99      )
% 27.79/3.99     ).
% 27.79/3.99  
% 27.79/3.99  %------ Negative definition of m1_subset_1 
% 27.79/3.99  fof(lit_def,axiom,
% 27.79/3.99      (! [X0,X1] : 
% 27.79/3.99        ( ~(m1_subset_1(X0,X1)) <=>
% 27.79/3.99             (
% 27.79/3.99                (
% 27.79/3.99                  ( X0=u1_struct_0(sK6) & X1=u1_struct_0(sK6) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=u1_struct_0(sK6) & X1=u1_struct_0(X2) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=u1_struct_0(X2) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=u1_struct_0(X2) & X1=u1_struct_0(sK6) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2,X3] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=u1_struct_0(X2) & X1=u1_struct_0(X3) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK2_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK2_0 & X1=u1_struct_0(sK6) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK2_0 & X1=u1_struct_0(X2) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK3_0 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK3_0 & X1=u1_struct_0(sK6) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99              ? [X2] : 
% 27.79/3.99                (
% 27.79/3.99                  ( X0=arAF0_sK3_0 & X1=u1_struct_0(X2) )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99             )
% 27.79/3.99        )
% 27.79/3.99      )
% 27.79/3.99     ).
% 27.79/3.99  
% 27.79/3.99  %------ Positive definition of r1_yellow_0 
% 27.79/3.99  fof(lit_def,axiom,
% 27.79/3.99      (! [X0,X1] : 
% 27.79/3.99        ( r1_yellow_0(X0,X1) <=>
% 27.79/3.99             (
% 27.79/3.99                (
% 27.79/3.99                  ( X0=sK6 & X1=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99               | 
% 27.79/3.99                (
% 27.79/3.99                  ( X1=sK8 )
% 27.79/3.99                )
% 27.79/3.99  
% 27.79/3.99             )
% 27.79/3.99        )
% 27.79/3.99      )
% 27.79/3.99     ).
% 27.79/3.99  
% 27.79/3.99  %------ Positive definition of l1_orders_2 
% 27.79/3.99  fof(lit_def,axiom,
% 27.79/3.99      (! [X0] : 
% 27.79/3.99        ( l1_orders_2(X0) <=>
% 27.79/3.99            $true
% 27.79/3.99        )
% 27.79/3.99      )
% 27.79/3.99     ).
% 27.79/3.99  
% 27.79/3.99  %------ Positive definition of r2_hidden 
% 27.79/3.99  fof(lit_def,axiom,
% 27.79/3.99      (! [X0,X1] : 
% 27.79/3.99        ( r2_hidden(X0,X1) <=>
% 27.79/3.99            $false
% 27.79/3.99        )
% 27.79/3.99      )
% 27.79/3.99     ).
% 27.79/3.99  
% 27.79/3.99  %------ Positive definition of v1_finset_1 
% 27.79/3.99  fof(lit_def,axiom,
% 27.79/3.99      (! [X0] : 
% 27.79/3.99        ( v1_finset_1(X0) <=>
% 27.79/3.99            $false
% 27.79/3.99        )
% 27.79/3.99      )
% 27.79/3.99     ).
% 27.79/3.99  % SZS output end Model for theBenchmark.p
% 27.79/3.99  ------                               Statistics
% 27.79/3.99  
% 27.79/3.99  ------ Selected
% 27.79/3.99  
% 27.79/3.99  total_time:                             3.385
% 27.79/3.99  
%------------------------------------------------------------------------------
