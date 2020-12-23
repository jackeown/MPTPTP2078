%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:16 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 969 expanded)
%              Number of clauses        :  139 ( 262 expanded)
%              Number of leaves         :   18 ( 236 expanded)
%              Depth                    :   25
%              Number of atoms          : 1088 (5680 expanded)
%              Number of equality atoms :  116 ( 132 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),X2)
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r3_lattices(X0,k16_lattice3(X0,sK6),k16_lattice3(X0,sK5))
          | ~ r3_lattices(X0,k15_lattice3(X0,sK5),k15_lattice3(X0,sK6)) )
        & r1_tarski(sK5,sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,X2),k16_lattice3(sK4,X1))
            | ~ r3_lattices(sK4,k15_lattice3(sK4,X1),k15_lattice3(sK4,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(sK4)
      & v4_lattice3(sK4)
      & v10_lattices(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) )
    & r1_tarski(sK5,sK6)
    & l3_lattices(sK4)
    & v4_lattice3(sK4)
    & v10_lattices(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f60,f59])).

fof(f91,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f94,plain,(
    l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f17,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f19])).

fof(f66,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f92,plain,(
    v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
                  & r2_hidden(sK0(X0,X1,X2),X2)
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r4_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r4_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f97,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r3_lattices(X0,X4,X1)
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f98,plain,(
    ! [X4,X2,X0] :
      ( r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f96,plain,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_922,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_34])).

cnf(c_923,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_922])).

cnf(c_31,negated_conjecture,
    ( l3_lattices(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_927,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_923,c_31])).

cnf(c_928,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_927])).

cnf(c_1969,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ r1_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_928])).

cnf(c_1,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_402,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_1,c_6])).

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_406,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_3,c_2])).

cnf(c_33,negated_conjecture,
    ( v10_lattices(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_789,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_406,c_33])).

cnf(c_790,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_794,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_34,c_31])).

cnf(c_795,plain,
    ( r1_lattices(sK4,X0,X1)
    | ~ r3_lattices(sK4,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_794])).

cnf(c_1975,plain,
    ( r1_lattices(sK4,X0_54,X1_54)
    | ~ r3_lattices(sK4,X0_54,X1_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_795])).

cnf(c_3803,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_1969,c_1975])).

cnf(c_13,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_880,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_881,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_885,plain,
    ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_31])).

cnf(c_886,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_885])).

cnf(c_1971,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | m1_subset_1(sK1(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_886])).

cnf(c_6865,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
    | r4_lattice3(sK4,X0_54,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3803,c_1971])).

cnf(c_6866,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_6865])).

cnf(c_28,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X2)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_32,negated_conjecture,
    ( v4_lattice3(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_533,plain,
    ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X1,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_534,plain,
    ( r3_lattices(sK4,X0,k15_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X1)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_538,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattices(sK4,X0,k15_lattice3(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_34,c_33,c_31])).

cnf(c_539,plain,
    ( r3_lattices(sK4,X0,k15_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_538])).

cnf(c_1984,plain,
    ( r3_lattices(sK4,X0_54,k15_lattice3(sK4,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ r2_hidden(X0_54,X0_55) ),
    inference(subtyping,[status(esa)],[c_539])).

cnf(c_6891,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
    | ~ m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
    | ~ r2_hidden(sK1(sK4,k15_lattice3(sK4,X0_55),X1_55),X0_55) ),
    inference(resolution,[status(thm)],[c_6866,c_1984])).

cnf(c_15,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_838,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_839,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_838])).

cnf(c_843,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_839,c_31])).

cnf(c_1973,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_843])).

cnf(c_2776,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
    | m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
    | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1971])).

cnf(c_15109,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
    | ~ r2_hidden(sK1(sK4,k15_lattice3(sK4,X0_55),X1_55),X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6891,c_1973,c_2776])).

cnf(c_12,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_901,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_34])).

cnf(c_902,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_901])).

cnf(c_906,plain,
    ( r2_hidden(sK1(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_902,c_31])).

cnf(c_907,plain,
    ( r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_906])).

cnf(c_1970,plain,
    ( r4_lattice3(sK4,X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0_54,X0_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_907])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,negated_conjecture,
    ( r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_387,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK5 != X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_30])).

cnf(c_388,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK6) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_1988,plain,
    ( ~ r2_hidden(X0_54,sK5)
    | r2_hidden(X0_54,sK6) ),
    inference(subtyping,[status(esa)],[c_388])).

cnf(c_2980,plain,
    ( r4_lattice3(sK4,X0_54,sK5)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | r2_hidden(sK1(sK4,X0_54,sK5),sK6) ),
    inference(resolution,[status(thm)],[c_1970,c_1988])).

cnf(c_15526,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
    | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(resolution,[status(thm)],[c_15109,c_2980])).

cnf(c_8,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_991,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_34])).

cnf(c_992,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_991])).

cnf(c_996,plain,
    ( r2_hidden(sK0(sK4,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_992,c_31])).

cnf(c_997,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_996])).

cnf(c_1966,plain,
    ( r3_lattice3(sK4,X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | r2_hidden(sK0(sK4,X0_54,X0_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_997])).

cnf(c_2547,plain,
    ( r3_lattice3(sK4,X0_54,X0_55) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,X0_54,X0_55),X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1966])).

cnf(c_2526,plain,
    ( r2_hidden(X0_54,sK5) != iProver_top
    | r2_hidden(X0_54,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1988])).

cnf(c_4342,plain,
    ( r3_lattice3(sK4,X0_54,sK5) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,X0_54,sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2547,c_2526])).

cnf(c_27,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_554,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_555,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0)
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_559,plain,
    ( ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r3_lattices(sK4,k16_lattice3(sK4,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_34,c_33,c_31])).

cnf(c_560,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0) ),
    inference(renaming,[status(thm)],[c_559])).

cnf(c_1983,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ r2_hidden(X0_54,X0_55) ),
    inference(subtyping,[status(esa)],[c_560])).

cnf(c_2531,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_54,X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(c_16,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_823,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_824,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_828,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_31])).

cnf(c_1974,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_828])).

cnf(c_2539,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_2538,plain,
    ( r1_lattices(sK4,X0_54,X1_54) = iProver_top
    | r3_lattices(sK4,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1975])).

cnf(c_3745,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54) = iProver_top
    | r3_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2539,c_2538])).

cnf(c_5618,plain,
    ( r1_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_54,X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_2531,c_3745])).

cnf(c_7,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1012,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_1013,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_1017,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1013,c_31])).

cnf(c_1018,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_1017])).

cnf(c_1965,plain,
    ( r3_lattice3(sK4,X0_54,X0_55)
    | ~ r1_lattices(sK4,X0_54,sK0(sK4,X0_54,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1018])).

cnf(c_2548,plain,
    ( r3_lattice3(sK4,X0_54,X0_55) = iProver_top
    | r1_lattices(sK4,X0_54,sK0(sK4,X0_54,X0_55)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1965])).

cnf(c_5661,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_55),X1_55) = iProver_top
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_5618,c_2548])).

cnf(c_2048,plain,
    ( m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_9,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_970,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_34])).

cnf(c_971,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_970])).

cnf(c_975,plain,
    ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_971,c_31])).

cnf(c_976,plain,
    ( r3_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_975])).

cnf(c_1967,plain,
    ( r3_lattice3(sK4,X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | m1_subset_1(sK0(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_976])).

cnf(c_2773,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_55),X1_55)
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
    | ~ m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_2774,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_55),X1_55) = iProver_top
    | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2773])).

cnf(c_7988,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,X0_55),X1_55) = iProver_top
    | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),X0_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5661,c_2048,c_2774])).

cnf(c_7996,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_7988])).

cnf(c_8014,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5)
    | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7996])).

cnf(c_17,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_700,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_701,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_705,plain,
    ( r2_hidden(X0,a_2_2_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r4_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_701,c_34,c_33,c_31])).

cnf(c_706,plain,
    ( ~ r4_lattice3(sK4,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_705])).

cnf(c_1977,plain,
    ( ~ r4_lattice3(sK4,X0_54,X0_55)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | r2_hidden(X0_54,a_2_2_lattice3(sK4,X0_55)) ),
    inference(subtyping,[status(esa)],[c_706])).

cnf(c_2536,plain,
    ( r4_lattice3(sK4,X0_54,X0_55) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_54,a_2_2_lattice3(sK4,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1977])).

cnf(c_26,plain,
    ( ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_575,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_32])).

cnf(c_576,plain,
    ( ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4)
    | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_580,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_576,c_34,c_33,c_31])).

cnf(c_1982,plain,
    ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_55)) = k15_lattice3(sK4,X0_55) ),
    inference(subtyping,[status(esa)],[c_580])).

cnf(c_3192,plain,
    ( r3_lattices(sK4,k15_lattice3(sK4,X0_55),X0_54) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_54,a_2_2_lattice3(sK4,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_2531])).

cnf(c_24,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_586,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_587,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ l3_lattices(sK4)
    | v2_struct_0(sK4)
    | ~ v10_lattices(sK4) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_591,plain,
    ( ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ r3_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_587,c_34,c_33,c_31])).

cnf(c_592,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_591])).

cnf(c_1034,plain,
    ( ~ r3_lattice3(sK4,X0,X1)
    | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_828,c_592])).

cnf(c_1964,plain,
    ( ~ r3_lattice3(sK4,X0_54,X0_55)
    | r3_lattices(sK4,X0_54,k16_lattice3(sK4,X0_55))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_1034])).

cnf(c_2549,plain,
    ( r3_lattice3(sK4,X0_54,X0_55) != iProver_top
    | r3_lattices(sK4,X0_54,k16_lattice3(sK4,X0_55)) = iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1964])).

cnf(c_29,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1989,negated_conjecture,
    ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
    | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2525,plain,
    ( r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) != iProver_top
    | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1989])).

cnf(c_4584,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top
    | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2549,c_2525])).

cnf(c_4728,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4584,c_2539])).

cnf(c_4731,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k15_lattice3(sK4,sK6),a_2_2_lattice3(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3192,c_4728])).

cnf(c_2540,plain,
    ( m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1973])).

cnf(c_5137,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | r2_hidden(k15_lattice3(sK4,sK6),a_2_2_lattice3(sK4,sK5)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4731,c_2540])).

cnf(c_5139,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) != iProver_top
    | r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2536,c_5137])).

cnf(c_5941,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_5942,plain,
    ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5941])).

cnf(c_6365,plain,
    ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
    | r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5139,c_5942])).

cnf(c_6366,plain,
    ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) != iProver_top
    | r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_6365])).

cnf(c_6367,plain,
    ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
    | ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6366])).

cnf(c_5991,plain,
    ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15526,c_8014,c_6367,c_5991,c_5941])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.74/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.00  
% 3.74/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/1.00  
% 3.74/1.00  ------  iProver source info
% 3.74/1.00  
% 3.74/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.74/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/1.00  git: non_committed_changes: false
% 3.74/1.00  git: last_make_outside_of_git: false
% 3.74/1.00  
% 3.74/1.00  ------ 
% 3.74/1.00  ------ Parsing...
% 3.74/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/1.00  
% 3.74/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.74/1.00  
% 3.74/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/1.00  
% 3.74/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.00  ------ Proving...
% 3.74/1.00  ------ Problem Properties 
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  clauses                                 26
% 3.74/1.00  conjectures                             1
% 3.74/1.00  EPR                                     1
% 3.74/1.00  Horn                                    20
% 3.74/1.00  unary                                   4
% 3.74/1.00  binary                                  5
% 3.74/1.00  lits                                    74
% 3.74/1.00  lits eq                                 5
% 3.74/1.00  fd_pure                                 0
% 3.74/1.00  fd_pseudo                               0
% 3.74/1.00  fd_cond                                 0
% 3.74/1.00  fd_pseudo_cond                          3
% 3.74/1.00  AC symbols                              0
% 3.74/1.00  
% 3.74/1.00  ------ Input Options Time Limit: Unbounded
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  ------ 
% 3.74/1.00  Current options:
% 3.74/1.00  ------ 
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  ------ Proving...
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  % SZS status Theorem for theBenchmark.p
% 3.74/1.00  
% 3.74/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/1.00  
% 3.74/1.00  fof(f5,axiom,(
% 3.74/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f25,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f5])).
% 3.74/1.00  
% 3.74/1.00  fof(f26,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f25])).
% 3.74/1.00  
% 3.74/1.00  fof(f46,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(nnf_transformation,[],[f26])).
% 3.74/1.00  
% 3.74/1.00  fof(f47,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(rectify,[],[f46])).
% 3.74/1.00  
% 3.74/1.00  fof(f48,plain,(
% 3.74/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f49,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 3.74/1.00  
% 3.74/1.00  fof(f76,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f49])).
% 3.74/1.00  
% 3.74/1.00  fof(f12,conjecture,(
% 3.74/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f13,negated_conjecture,(
% 3.74/1.00    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 3.74/1.00    inference(negated_conjecture,[],[f12])).
% 3.74/1.00  
% 3.74/1.00  fof(f39,plain,(
% 3.74/1.00    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f13])).
% 3.74/1.00  
% 3.74/1.00  fof(f40,plain,(
% 3.74/1.00    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f39])).
% 3.74/1.00  
% 3.74/1.00  fof(f60,plain,(
% 3.74/1.00    ( ! [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK6),k16_lattice3(X0,sK5)) | ~r3_lattices(X0,k15_lattice3(X0,sK5),k15_lattice3(X0,sK6))) & r1_tarski(sK5,sK6))) )),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f59,plain,(
% 3.74/1.00    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : ((~r3_lattices(sK4,k16_lattice3(sK4,X2),k16_lattice3(sK4,X1)) | ~r3_lattices(sK4,k15_lattice3(sK4,X1),k15_lattice3(sK4,X2))) & r1_tarski(X1,X2)) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4))),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f61,plain,(
% 3.74/1.00    ((~r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) | ~r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))) & r1_tarski(sK5,sK6)) & l3_lattices(sK4) & v4_lattice3(sK4) & v10_lattices(sK4) & ~v2_struct_0(sK4)),
% 3.74/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f40,f60,f59])).
% 3.74/1.00  
% 3.74/1.00  fof(f91,plain,(
% 3.74/1.00    ~v2_struct_0(sK4)),
% 3.74/1.00    inference(cnf_transformation,[],[f61])).
% 3.74/1.00  
% 3.74/1.00  fof(f94,plain,(
% 3.74/1.00    l3_lattices(sK4)),
% 3.74/1.00    inference(cnf_transformation,[],[f61])).
% 3.74/1.00  
% 3.74/1.00  fof(f2,axiom,(
% 3.74/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f15,plain,(
% 3.74/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.74/1.00    inference(pure_predicate_removal,[],[f2])).
% 3.74/1.00  
% 3.74/1.00  fof(f16,plain,(
% 3.74/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.74/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.74/1.00  
% 3.74/1.00  fof(f17,plain,(
% 3.74/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 3.74/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.74/1.00  
% 3.74/1.00  fof(f19,plain,(
% 3.74/1.00    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.74/1.00    inference(ennf_transformation,[],[f17])).
% 3.74/1.00  
% 3.74/1.00  fof(f20,plain,(
% 3.74/1.00    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.74/1.00    inference(flattening,[],[f19])).
% 3.74/1.00  
% 3.74/1.00  fof(f66,plain,(
% 3.74/1.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f20])).
% 3.74/1.00  
% 3.74/1.00  fof(f3,axiom,(
% 3.74/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f21,plain,(
% 3.74/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f3])).
% 3.74/1.00  
% 3.74/1.00  fof(f22,plain,(
% 3.74/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f21])).
% 3.74/1.00  
% 3.74/1.00  fof(f41,plain,(
% 3.74/1.00    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(nnf_transformation,[],[f22])).
% 3.74/1.00  
% 3.74/1.00  fof(f67,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f41])).
% 3.74/1.00  
% 3.74/1.00  fof(f64,plain,(
% 3.74/1.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f20])).
% 3.74/1.00  
% 3.74/1.00  fof(f65,plain,(
% 3.74/1.00    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f20])).
% 3.74/1.00  
% 3.74/1.00  fof(f92,plain,(
% 3.74/1.00    v10_lattices(sK4)),
% 3.74/1.00    inference(cnf_transformation,[],[f61])).
% 3.74/1.00  
% 3.74/1.00  fof(f74,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f49])).
% 3.74/1.00  
% 3.74/1.00  fof(f11,axiom,(
% 3.74/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f37,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f11])).
% 3.74/1.00  
% 3.74/1.00  fof(f38,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f37])).
% 3.74/1.00  
% 3.74/1.00  fof(f89,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f38])).
% 3.74/1.00  
% 3.74/1.00  fof(f93,plain,(
% 3.74/1.00    v4_lattice3(sK4)),
% 3.74/1.00    inference(cnf_transformation,[],[f61])).
% 3.74/1.00  
% 3.74/1.00  fof(f6,axiom,(
% 3.74/1.00    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f27,plain,(
% 3.74/1.00    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f6])).
% 3.74/1.00  
% 3.74/1.00  fof(f28,plain,(
% 3.74/1.00    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f27])).
% 3.74/1.00  
% 3.74/1.00  fof(f77,plain,(
% 3.74/1.00    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f28])).
% 3.74/1.00  
% 3.74/1.00  fof(f75,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f49])).
% 3.74/1.00  
% 3.74/1.00  fof(f1,axiom,(
% 3.74/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f14,plain,(
% 3.74/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.74/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.74/1.00  
% 3.74/1.00  fof(f18,plain,(
% 3.74/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.74/1.00    inference(ennf_transformation,[],[f14])).
% 3.74/1.00  
% 3.74/1.00  fof(f62,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f18])).
% 3.74/1.00  
% 3.74/1.00  fof(f95,plain,(
% 3.74/1.00    r1_tarski(sK5,sK6)),
% 3.74/1.00    inference(cnf_transformation,[],[f61])).
% 3.74/1.00  
% 3.74/1.00  fof(f4,axiom,(
% 3.74/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f23,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f4])).
% 3.74/1.00  
% 3.74/1.00  fof(f24,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f23])).
% 3.74/1.00  
% 3.74/1.00  fof(f42,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(nnf_transformation,[],[f24])).
% 3.74/1.00  
% 3.74/1.00  fof(f43,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(rectify,[],[f42])).
% 3.74/1.00  
% 3.74/1.00  fof(f44,plain,(
% 3.74/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f45,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.74/1.00  
% 3.74/1.00  fof(f71,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f45])).
% 3.74/1.00  
% 3.74/1.00  fof(f90,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f38])).
% 3.74/1.00  
% 3.74/1.00  fof(f7,axiom,(
% 3.74/1.00    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f29,plain,(
% 3.74/1.00    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f7])).
% 3.74/1.00  
% 3.74/1.00  fof(f30,plain,(
% 3.74/1.00    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f29])).
% 3.74/1.00  
% 3.74/1.00  fof(f78,plain,(
% 3.74/1.00    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f30])).
% 3.74/1.00  
% 3.74/1.00  fof(f72,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f45])).
% 3.74/1.00  
% 3.74/1.00  fof(f70,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f45])).
% 3.74/1.00  
% 3.74/1.00  fof(f8,axiom,(
% 3.74/1.00    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f31,plain,(
% 3.74/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 3.74/1.00    inference(ennf_transformation,[],[f8])).
% 3.74/1.00  
% 3.74/1.00  fof(f32,plain,(
% 3.74/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.74/1.00    inference(flattening,[],[f31])).
% 3.74/1.00  
% 3.74/1.00  fof(f50,plain,(
% 3.74/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.74/1.00    inference(nnf_transformation,[],[f32])).
% 3.74/1.00  
% 3.74/1.00  fof(f51,plain,(
% 3.74/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.74/1.00    inference(rectify,[],[f50])).
% 3.74/1.00  
% 3.74/1.00  fof(f52,plain,(
% 3.74/1.00    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f53,plain,(
% 3.74/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.74/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 3.74/1.00  
% 3.74/1.00  fof(f82,plain,(
% 3.74/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f53])).
% 3.74/1.00  
% 3.74/1.00  fof(f97,plain,(
% 3.74/1.00    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.74/1.00    inference(equality_resolution,[],[f82])).
% 3.74/1.00  
% 3.74/1.00  fof(f10,axiom,(
% 3.74/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f35,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f10])).
% 3.74/1.00  
% 3.74/1.00  fof(f36,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f88,plain,(
% 3.74/1.00    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f36])).
% 3.74/1.00  
% 3.74/1.00  fof(f9,axiom,(
% 3.74/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 3.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f33,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f9])).
% 3.74/1.00  
% 3.74/1.00  fof(f34,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f33])).
% 3.74/1.00  
% 3.74/1.00  fof(f54,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(nnf_transformation,[],[f34])).
% 3.74/1.00  
% 3.74/1.00  fof(f55,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f54])).
% 3.74/1.00  
% 3.74/1.00  fof(f56,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(rectify,[],[f55])).
% 3.74/1.00  
% 3.74/1.00  fof(f57,plain,(
% 3.74/1.00    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f58,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).
% 3.74/1.00  
% 3.74/1.00  fof(f84,plain,(
% 3.74/1.00    ( ! [X4,X2,X0,X1] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f58])).
% 3.74/1.00  
% 3.74/1.00  fof(f98,plain,(
% 3.74/1.00    ( ! [X4,X2,X0] : (r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(equality_resolution,[],[f84])).
% 3.74/1.00  
% 3.74/1.00  fof(f96,plain,(
% 3.74/1.00    ~r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) | ~r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6))),
% 3.74/1.00    inference(cnf_transformation,[],[f61])).
% 3.74/1.00  
% 3.74/1.00  cnf(c_11,plain,
% 3.74/1.00      ( r4_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_34,negated_conjecture,
% 3.74/1.00      ( ~ v2_struct_0(sK4) ),
% 3.74/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_922,plain,
% 3.74/1.00      ( r4_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_34]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_923,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ l3_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_922]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_31,negated_conjecture,
% 3.74/1.00      ( l3_lattices(sK4) ),
% 3.74/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_927,plain,
% 3.74/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.74/1.00      | r4_lattice3(sK4,X0,X1) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_923,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_928,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ r1_lattices(sK4,sK1(sK4,X0,X1),X0)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_927]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1969,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | ~ r1_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_928]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1,plain,
% 3.74/1.00      ( ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0)
% 3.74/1.00      | v9_lattices(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_6,plain,
% 3.74/1.00      ( r1_lattices(X0,X1,X2)
% 3.74/1.00      | ~ r3_lattices(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ v6_lattices(X0)
% 3.74/1.00      | ~ v8_lattices(X0)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v9_lattices(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_402,plain,
% 3.74/1.00      ( r1_lattices(X0,X1,X2)
% 3.74/1.00      | ~ r3_lattices(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ v6_lattices(X0)
% 3.74/1.00      | ~ v8_lattices(X0)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0) ),
% 3.74/1.00      inference(resolution,[status(thm)],[c_1,c_6]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3,plain,
% 3.74/1.00      ( v6_lattices(X0)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2,plain,
% 3.74/1.00      ( v8_lattices(X0)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_406,plain,
% 3.74/1.00      ( r1_lattices(X0,X1,X2)
% 3.74/1.00      | ~ r3_lattices(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_402,c_3,c_2]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_33,negated_conjecture,
% 3.74/1.00      ( v10_lattices(sK4) ),
% 3.74/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_789,plain,
% 3.74/1.00      ( r1_lattices(X0,X1,X2)
% 3.74/1.00      | ~ r3_lattices(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_406,c_33]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_790,plain,
% 3.74/1.00      ( r1_lattices(sK4,X0,X1)
% 3.74/1.00      | ~ r3_lattices(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.74/1.00      | ~ l3_lattices(sK4)
% 3.74/1.00      | v2_struct_0(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_789]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_794,plain,
% 3.74/1.00      ( r1_lattices(sK4,X0,X1)
% 3.74/1.00      | ~ r3_lattices(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_790,c_34,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_795,plain,
% 3.74/1.00      ( r1_lattices(sK4,X0,X1)
% 3.74/1.00      | ~ r3_lattices(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_794]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1975,plain,
% 3.74/1.00      ( r1_lattices(sK4,X0_54,X1_54)
% 3.74/1.00      | ~ r3_lattices(sK4,X0_54,X1_54)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_795]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3803,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(sK1(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(resolution,[status(thm)],[c_1969,c_1975]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_13,plain,
% 3.74/1.00      ( r4_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_880,plain,
% 3.74/1.00      ( r4_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_881,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 3.74/1.00      | ~ l3_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_880]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_885,plain,
% 3.74/1.00      ( m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r4_lattice3(sK4,X0,X1) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_881,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_886,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | m1_subset_1(sK1(sK4,X0,X1),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_885]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1971,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | m1_subset_1(sK1(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_886]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_6865,plain,
% 3.74/1.00      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
% 3.74/1.00      | r4_lattice3(sK4,X0_54,X0_55) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_3803,c_1971]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_6866,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | ~ r3_lattices(sK4,sK1(sK4,X0_54,X0_55),X0_54)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_6865]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_28,plain,
% 3.74/1.00      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ r2_hidden(X1,X2)
% 3.74/1.00      | ~ v4_lattice3(X0)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_32,negated_conjecture,
% 3.74/1.00      ( v4_lattice3(sK4) ),
% 3.74/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_533,plain,
% 3.74/1.00      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ r2_hidden(X1,X2)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_534,plain,
% 3.74/1.00      ( r3_lattices(sK4,X0,k15_lattice3(sK4,X1))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ r2_hidden(X0,X1)
% 3.74/1.00      | ~ l3_lattices(sK4)
% 3.74/1.00      | v2_struct_0(sK4)
% 3.74/1.00      | ~ v10_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_533]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_538,plain,
% 3.74/1.00      ( ~ r2_hidden(X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r3_lattices(sK4,X0,k15_lattice3(sK4,X1)) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_534,c_34,c_33,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_539,plain,
% 3.74/1.00      ( r3_lattices(sK4,X0,k15_lattice3(sK4,X1))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ r2_hidden(X0,X1) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_538]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1984,plain,
% 3.74/1.00      ( r3_lattices(sK4,X0_54,k15_lattice3(sK4,X0_55))
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | ~ r2_hidden(X0_54,X0_55) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_539]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_6891,plain,
% 3.74/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
% 3.74/1.00      | ~ m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4))
% 3.74/1.00      | ~ r2_hidden(sK1(sK4,k15_lattice3(sK4,X0_55),X1_55),X0_55) ),
% 3.74/1.00      inference(resolution,[status(thm)],[c_6866,c_1984]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_15,plain,
% 3.74/1.00      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_838,plain,
% 3.74/1.00      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_34]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_839,plain,
% 3.74/1.00      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4))
% 3.74/1.00      | ~ l3_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_838]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_843,plain,
% 3.74/1.00      ( m1_subset_1(k15_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_839,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1973,plain,
% 3.74/1.00      ( m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_843]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2776,plain,
% 3.74/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
% 3.74/1.00      | m1_subset_1(sK1(sK4,k15_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_1971]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_15109,plain,
% 3.74/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,X0_55),X1_55)
% 3.74/1.00      | ~ r2_hidden(sK1(sK4,k15_lattice3(sK4,X0_55),X1_55),X0_55) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_6891,c_1973,c_2776]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_12,plain,
% 3.74/1.00      ( r4_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_901,plain,
% 3.74/1.00      ( r4_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_34]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_902,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(sK1(sK4,X0,X1),X1)
% 3.74/1.00      | ~ l3_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_901]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_906,plain,
% 3.74/1.00      ( r2_hidden(sK1(sK4,X0,X1),X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r4_lattice3(sK4,X0,X1) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_902,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_907,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(sK1(sK4,X0,X1),X1) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_906]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1970,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(sK1(sK4,X0_54,X0_55),X0_55) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_907]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_0,plain,
% 3.74/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.74/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_30,negated_conjecture,
% 3.74/1.00      ( r1_tarski(sK5,sK6) ),
% 3.74/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_387,plain,
% 3.74/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK5 != X1 | sK6 != X2 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_30]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_388,plain,
% 3.74/1.00      ( ~ r2_hidden(X0,sK5) | r2_hidden(X0,sK6) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_387]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1988,plain,
% 3.74/1.00      ( ~ r2_hidden(X0_54,sK5) | r2_hidden(X0_54,sK6) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_388]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2980,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0_54,sK5)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(sK1(sK4,X0_54,sK5),sK6) ),
% 3.74/1.00      inference(resolution,[status(thm)],[c_1970,c_1988]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_15526,plain,
% 3.74/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
% 3.74/1.00      | ~ m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(resolution,[status(thm)],[c_15109,c_2980]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_8,plain,
% 3.74/1.00      ( r3_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_991,plain,
% 3.74/1.00      ( r3_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_34]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_992,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(sK0(sK4,X0,X1),X1)
% 3.74/1.00      | ~ l3_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_991]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_996,plain,
% 3.74/1.00      ( r2_hidden(sK0(sK4,X0,X1),X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r3_lattice3(sK4,X0,X1) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_992,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_997,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(sK0(sK4,X0,X1),X1) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_996]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1966,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(sK0(sK4,X0_54,X0_55),X0_55) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_997]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2547,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0_54,X0_55) = iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | r2_hidden(sK0(sK4,X0_54,X0_55),X0_55) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1966]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2526,plain,
% 3.74/1.00      ( r2_hidden(X0_54,sK5) != iProver_top
% 3.74/1.00      | r2_hidden(X0_54,sK6) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1988]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_4342,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0_54,sK5) = iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | r2_hidden(sK0(sK4,X0_54,sK5),sK6) = iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2547,c_2526]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_27,plain,
% 3.74/1.00      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 3.74/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.00      | ~ r2_hidden(X2,X1)
% 3.74/1.00      | ~ v4_lattice3(X0)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_554,plain,
% 3.74/1.00      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 3.74/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.74/1.00      | ~ r2_hidden(X2,X1)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_555,plain,
% 3.74/1.00      ( r3_lattices(sK4,k16_lattice3(sK4,X0),X1)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.74/1.00      | ~ r2_hidden(X1,X0)
% 3.74/1.00      | ~ l3_lattices(sK4)
% 3.74/1.00      | v2_struct_0(sK4)
% 3.74/1.00      | ~ v10_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_554]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_559,plain,
% 3.74/1.00      ( ~ r2_hidden(X1,X0)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.74/1.00      | r3_lattices(sK4,k16_lattice3(sK4,X0),X1) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_555,c_34,c_33,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_560,plain,
% 3.74/1.00      ( r3_lattices(sK4,k16_lattice3(sK4,X0),X1)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.74/1.00      | ~ r2_hidden(X1,X0) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_559]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1983,plain,
% 3.74/1.00      ( r3_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | ~ r2_hidden(X0_54,X0_55) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_560]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2531,plain,
% 3.74/1.00      ( r3_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54) = iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | r2_hidden(X0_54,X0_55) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_16,plain,
% 3.74/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_823,plain,
% 3.74/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_34]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_824,plain,
% 3.74/1.00      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4))
% 3.74/1.00      | ~ l3_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_823]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_828,plain,
% 3.74/1.00      ( m1_subset_1(k16_lattice3(sK4,X0),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_824,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1974,plain,
% 3.74/1.00      ( m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_828]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2539,plain,
% 3.74/1.00      ( m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2538,plain,
% 3.74/1.00      ( r1_lattices(sK4,X0_54,X1_54) = iProver_top
% 3.74/1.00      | r3_lattices(sK4,X0_54,X1_54) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | m1_subset_1(X1_54,u1_struct_0(sK4)) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1975]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3745,plain,
% 3.74/1.00      ( r1_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54) = iProver_top
% 3.74/1.00      | r3_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2539,c_2538]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5618,plain,
% 3.74/1.00      ( r1_lattices(sK4,k16_lattice3(sK4,X0_55),X0_54) = iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | r2_hidden(X0_54,X0_55) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2531,c_3745]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_7,plain,
% 3.74/1.00      ( r3_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1012,plain,
% 3.74/1.00      ( r3_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_34]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1013,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ l3_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_1012]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1017,plain,
% 3.74/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.74/1.00      | r3_lattice3(sK4,X0,X1) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_1013,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1018,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ r1_lattices(sK4,X0,sK0(sK4,X0,X1))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_1017]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1965,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | ~ r1_lattices(sK4,X0_54,sK0(sK4,X0_54,X0_55))
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_1018]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2548,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0_54,X0_55) = iProver_top
% 3.74/1.00      | r1_lattices(sK4,X0_54,sK0(sK4,X0_54,X0_55)) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1965]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5661,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_55),X1_55) = iProver_top
% 3.74/1.00      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),X0_55) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_5618,c_2548]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2048,plain,
% 3.74/1.00      ( m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_9,plain,
% 3.74/1.00      ( r3_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_970,plain,
% 3.74/1.00      ( r3_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_34]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_971,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 3.74/1.00      | ~ l3_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_970]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_975,plain,
% 3.74/1.00      ( m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r3_lattice3(sK4,X0,X1) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_971,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_976,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | m1_subset_1(sK0(sK4,X0,X1),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_975]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1967,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | m1_subset_1(sK0(sK4,X0_54,X0_55),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_976]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2773,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_55),X1_55)
% 3.74/1.00      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_1967]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2774,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_55),X1_55) = iProver_top
% 3.74/1.00      | m1_subset_1(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),u1_struct_0(sK4)) = iProver_top
% 3.74/1.00      | m1_subset_1(k16_lattice3(sK4,X0_55),u1_struct_0(sK4)) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_2773]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_7988,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,X0_55),X1_55) = iProver_top
% 3.74/1.00      | r2_hidden(sK0(sK4,k16_lattice3(sK4,X0_55),X1_55),X0_55) != iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_5661,c_2048,c_2774]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_7996,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) = iProver_top
% 3.74/1.00      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_4342,c_7988]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_8014,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5)
% 3.74/1.00      | ~ m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7996]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_17,plain,
% 3.74/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.74/1.00      | ~ v4_lattice3(X0)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_700,plain,
% 3.74/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_701,plain,
% 3.74/1.00      ( ~ r4_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.74/1.00      | ~ l3_lattices(sK4)
% 3.74/1.00      | v2_struct_0(sK4)
% 3.74/1.00      | ~ v10_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_700]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_705,plain,
% 3.74/1.00      ( r2_hidden(X0,a_2_2_lattice3(sK4,X1))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ r4_lattice3(sK4,X0,X1) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_701,c_34,c_33,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_706,plain,
% 3.74/1.00      ( ~ r4_lattice3(sK4,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(X0,a_2_2_lattice3(sK4,X1)) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_705]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1977,plain,
% 3.74/1.00      ( ~ r4_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 3.74/1.00      | r2_hidden(X0_54,a_2_2_lattice3(sK4,X0_55)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_706]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2536,plain,
% 3.74/1.00      ( r4_lattice3(sK4,X0_54,X0_55) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | r2_hidden(X0_54,a_2_2_lattice3(sK4,X0_55)) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1977]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_26,plain,
% 3.74/1.00      ( ~ v4_lattice3(X0)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0)
% 3.74/1.00      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
% 3.74/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_575,plain,
% 3.74/1.00      ( ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0)
% 3.74/1.00      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_32]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_576,plain,
% 3.74/1.00      ( ~ l3_lattices(sK4)
% 3.74/1.00      | v2_struct_0(sK4)
% 3.74/1.00      | ~ v10_lattices(sK4)
% 3.74/1.00      | k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_575]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_580,plain,
% 3.74/1.00      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0)) = k15_lattice3(sK4,X0) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_576,c_34,c_33,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1982,plain,
% 3.74/1.00      ( k16_lattice3(sK4,a_2_2_lattice3(sK4,X0_55)) = k15_lattice3(sK4,X0_55) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_580]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3192,plain,
% 3.74/1.00      ( r3_lattices(sK4,k15_lattice3(sK4,X0_55),X0_54) = iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | r2_hidden(X0_54,a_2_2_lattice3(sK4,X0_55)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_1982,c_2531]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_24,plain,
% 3.74/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.74/1.00      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 3.74/1.00      | ~ v4_lattice3(X0)
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_586,plain,
% 3.74/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.74/1.00      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.74/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.74/1.00      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 3.74/1.00      | ~ l3_lattices(X0)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ v10_lattices(X0)
% 3.74/1.00      | sK4 != X0 ),
% 3.74/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_587,plain,
% 3.74/1.00      ( ~ r3_lattice3(sK4,X0,X1)
% 3.74/1.00      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4))
% 3.74/1.00      | ~ l3_lattices(sK4)
% 3.74/1.00      | v2_struct_0(sK4)
% 3.74/1.00      | ~ v10_lattices(sK4) ),
% 3.74/1.00      inference(unflattening,[status(thm)],[c_586]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_591,plain,
% 3.74/1.00      ( ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.74/1.00      | ~ r3_lattice3(sK4,X0,X1) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_587,c_34,c_33,c_31]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_592,plain,
% 3.74/1.00      ( ~ r3_lattice3(sK4,X0,X1)
% 3.74/1.00      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 3.74/1.00      | ~ m1_subset_1(k16_lattice3(sK4,X1),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_591]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1034,plain,
% 3.74/1.00      ( ~ r3_lattice3(sK4,X0,X1)
% 3.74/1.00      | r3_lattices(sK4,X0,k16_lattice3(sK4,X1))
% 3.74/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(backward_subsumption_resolution,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_828,c_592]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1964,plain,
% 3.74/1.00      ( ~ r3_lattice3(sK4,X0_54,X0_55)
% 3.74/1.00      | r3_lattices(sK4,X0_54,k16_lattice3(sK4,X0_55))
% 3.74/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_1034]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2549,plain,
% 3.74/1.00      ( r3_lattice3(sK4,X0_54,X0_55) != iProver_top
% 3.74/1.00      | r3_lattices(sK4,X0_54,k16_lattice3(sK4,X0_55)) = iProver_top
% 3.74/1.00      | m1_subset_1(X0_54,u1_struct_0(sK4)) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1964]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_29,negated_conjecture,
% 3.74/1.00      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
% 3.74/1.00      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
% 3.74/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1989,negated_conjecture,
% 3.74/1.00      ( ~ r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5))
% 3.74/1.00      | ~ r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_29]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2525,plain,
% 3.74/1.00      ( r3_lattices(sK4,k16_lattice3(sK4,sK6),k16_lattice3(sK4,sK5)) != iProver_top
% 3.74/1.00      | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1989]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_4584,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.74/1.00      | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top
% 3.74/1.00      | m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2549,c_2525]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_4728,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.74/1.00      | r3_lattices(sK4,k15_lattice3(sK4,sK5),k15_lattice3(sK4,sK6)) != iProver_top ),
% 3.74/1.00      inference(forward_subsumption_resolution,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_4584,c_2539]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_4731,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.74/1.00      | m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top
% 3.74/1.00      | r2_hidden(k15_lattice3(sK4,sK6),a_2_2_lattice3(sK4,sK5)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_3192,c_4728]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2540,plain,
% 3.74/1.00      ( m1_subset_1(k15_lattice3(sK4,X0_55),u1_struct_0(sK4)) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1973]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5137,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.74/1.00      | r2_hidden(k15_lattice3(sK4,sK6),a_2_2_lattice3(sK4,sK5)) != iProver_top ),
% 3.74/1.00      inference(forward_subsumption_resolution,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_4731,c_2540]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5139,plain,
% 3.74/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) != iProver_top
% 3.74/1.00      | r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.74/1.00      | m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2536,c_5137]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5941,plain,
% 3.74/1.00      ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_1973]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5942,plain,
% 3.74/1.00      ( m1_subset_1(k15_lattice3(sK4,sK6),u1_struct_0(sK4)) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_5941]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_6365,plain,
% 3.74/1.00      ( r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top
% 3.74/1.00      | r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) != iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_5139,c_5942]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_6366,plain,
% 3.74/1.00      ( r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5) != iProver_top
% 3.74/1.00      | r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) != iProver_top ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_6365]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_6367,plain,
% 3.74/1.00      ( ~ r4_lattice3(sK4,k15_lattice3(sK4,sK6),sK5)
% 3.74/1.00      | ~ r3_lattice3(sK4,k16_lattice3(sK4,sK6),sK5) ),
% 3.74/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6366]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5991,plain,
% 3.74/1.00      ( m1_subset_1(k16_lattice3(sK4,sK6),u1_struct_0(sK4)) ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_1974]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(contradiction,plain,
% 3.74/1.00      ( $false ),
% 3.74/1.00      inference(minisat,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_15526,c_8014,c_6367,c_5991,c_5941]) ).
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/1.00  
% 3.74/1.00  ------                               Statistics
% 3.74/1.00  
% 3.74/1.00  ------ Selected
% 3.74/1.00  
% 3.74/1.00  total_time:                             0.464
% 3.74/1.00  
%------------------------------------------------------------------------------
