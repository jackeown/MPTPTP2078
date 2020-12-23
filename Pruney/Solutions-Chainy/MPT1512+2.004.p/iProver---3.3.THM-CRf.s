%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:16 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  280 (2276 expanded)
%              Number of clauses        :  195 ( 617 expanded)
%              Number of leaves         :   17 ( 556 expanded)
%              Depth                    :   29
%              Number of atoms          : 1235 (13418 expanded)
%              Number of equality atoms :  227 ( 453 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   14 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f55,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r3_lattices(X0,k16_lattice3(X0,sK5),k16_lattice3(X0,sK4))
          | ~ r3_lattices(X0,k15_lattice3(X0,sK4),k15_lattice3(X0,sK5)) )
        & r1_tarski(sK4,sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
          ( ( ~ r3_lattices(sK3,k16_lattice3(sK3,X2),k16_lattice3(sK3,X1))
            | ~ r3_lattices(sK3,k15_lattice3(sK3,X1),k15_lattice3(sK3,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(sK3)
      & v4_lattice3(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
      | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) )
    & r1_tarski(sK4,sK5)
    & l3_lattices(sK3)
    & v4_lattice3(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f55,f54])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f61,plain,(
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

fof(f62,plain,(
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

fof(f59,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
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
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
    | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
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

fof(f88,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_832,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_833,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_832])).

cnf(c_27,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_837,plain,
    ( r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_833,c_27])).

cnf(c_838,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_837])).

cnf(c_2017,plain,
    ( r3_lattice3(sK3,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0_53,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_838])).

cnf(c_2477,plain,
    ( r3_lattice3(sK3,X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,X0_53,X0_54),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2017])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK4 != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_337,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_2036,plain,
    ( ~ r2_hidden(X0_53,sK4)
    | r2_hidden(X0_53,sK5) ),
    inference(subtyping,[status(esa)],[c_337])).

cnf(c_2459,plain,
    ( r2_hidden(X0_53,sK4) != iProver_top
    | r2_hidden(X0_53,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2036])).

cnf(c_4244,plain,
    ( r3_lattice3(sK3,X0_53,sK4) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,X0_53,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_2459])).

cnf(c_22,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_28,negated_conjecture,
    ( v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_509,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_510,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_29,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_514,plain,
    ( ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r3_lattices(sK3,k16_lattice3(sK3,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_30,c_29,c_27])).

cnf(c_515,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0) ),
    inference(renaming,[status(thm)],[c_514])).

cnf(c_2031,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ r2_hidden(X0_53,X0_54) ),
    inference(subtyping,[status(esa)],[c_515])).

cnf(c_2464,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2031])).

cnf(c_16,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_664,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_665,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_669,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_27])).

cnf(c_2025,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_669])).

cnf(c_2469,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2025])).

cnf(c_1,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(cnf_transformation,[],[f62])).

cnf(c_351,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_2,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_355,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_351,c_3,c_2])).

cnf(c_630,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_355,c_29])).

cnf(c_631,plain,
    ( r1_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_630])).

cnf(c_635,plain,
    ( r1_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_631,c_30,c_27])).

cnf(c_636,plain,
    ( r1_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_635])).

cnf(c_2026,plain,
    ( r1_lattices(sK3,X0_53,X1_53)
    | ~ r3_lattices(sK3,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_636])).

cnf(c_2468,plain,
    ( r1_lattices(sK3,X0_53,X1_53) = iProver_top
    | r3_lattices(sK3,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2026])).

cnf(c_3752,plain,
    ( r1_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53) = iProver_top
    | r3_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_2468])).

cnf(c_4697,plain,
    ( r1_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2464,c_3752])).

cnf(c_7,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_853,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_30])).

cnf(c_854,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_858,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_27])).

cnf(c_859,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_858])).

cnf(c_2016,plain,
    ( r3_lattice3(sK3,X0_53,X0_54)
    | ~ r1_lattices(sK3,X0_53,sK0(sK3,X0_53,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_859])).

cnf(c_2478,plain,
    ( r3_lattice3(sK3,X0_53,X0_54) = iProver_top
    | r1_lattices(sK3,X0_53,sK0(sK3,X0_53,X0_54)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2016])).

cnf(c_4713,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_4697,c_2478])).

cnf(c_2085,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2025])).

cnf(c_9,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_811,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_812,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_811])).

cnf(c_816,plain,
    ( m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_812,c_27])).

cnf(c_817,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_816])).

cnf(c_2018,plain,
    ( r3_lattice3(sK3,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_53,X0_54),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_817])).

cnf(c_2537,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_54),X1_54)
    | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_2538,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2537])).

cnf(c_6482,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_54),X1_54) = iProver_top
    | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4713,c_2085,c_2538])).

cnf(c_6490,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) = iProver_top
    | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4244,c_6482])).

cnf(c_2987,plain,
    ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_2988,plain,
    ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2987])).

cnf(c_6940,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6490,c_2988])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_449,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK2(X0,X1,X2) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_450,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3)
    | sK2(X0,sK3,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_454,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
    | sK2(X0,sK3,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_30,c_29,c_27])).

cnf(c_2034,plain,
    ( ~ r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54))
    | sK2(X0_53,sK3,X0_54) = X0_53 ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_2461,plain,
    ( sK2(X0_53,sK3,X0_54) = X0_53
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2034])).

cnf(c_4243,plain,
    ( sK2(sK0(sK3,X0_53,a_2_2_lattice3(sK3,X0_54)),sK3,X0_54) = sK0(sK3,X0_53,a_2_2_lattice3(sK3,X0_54))
    | r3_lattice3(sK3,X0_53,a_2_2_lattice3(sK3,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_2461])).

cnf(c_21,plain,
    ( ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_530,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_531,plain,
    ( ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3)
    | k16_lattice3(sK3,a_2_2_lattice3(sK3,X0)) = k15_lattice3(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_535,plain,
    ( k16_lattice3(sK3,a_2_2_lattice3(sK3,X0)) = k15_lattice3(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_30,c_29,c_27])).

cnf(c_2030,plain,
    ( k16_lattice3(sK3,a_2_2_lattice3(sK3,X0_54)) = k15_lattice3(sK3,X0_54) ),
    inference(subtyping,[status(esa)],[c_535])).

cnf(c_24,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_467,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_468,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_30,c_29,c_27])).

cnf(c_473,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_472])).

cnf(c_2033,plain,
    ( ~ r3_lattice3(sK3,X0_53,X0_54)
    | r3_lattices(sK3,X0_53,k16_lattice3(sK3,X0_54))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_473])).

cnf(c_2462,plain,
    ( r3_lattice3(sK3,X0_53,X0_54) != iProver_top
    | r3_lattices(sK3,X0_53,k16_lattice3(sK3,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2033])).

cnf(c_2826,plain,
    ( r3_lattice3(sK3,X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
    | r3_lattices(sK3,X0_53,k15_lattice3(sK3,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_2462])).

cnf(c_5933,plain,
    ( sK2(sK0(sK3,X0_53,a_2_2_lattice3(sK3,X0_54)),sK3,X0_54) = sK0(sK3,X0_53,a_2_2_lattice3(sK3,X0_54))
    | r3_lattices(sK3,X0_53,k15_lattice3(sK3,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4243,c_2826])).

cnf(c_25,negated_conjecture,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
    | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2037,negated_conjecture,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
    | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2458,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4)) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2037])).

cnf(c_2827,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2462,c_2458])).

cnf(c_6323,plain,
    ( sK2(sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK3,sK5) = sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5))
    | r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k15_lattice3(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5933,c_2827])).

cnf(c_15,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_679,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_680,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_684,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_680,c_27])).

cnf(c_2024,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_684])).

cnf(c_2088,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2024])).

cnf(c_2090,plain,
    ( m1_subset_1(k15_lattice3(sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_6382,plain,
    ( sK2(sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK3,sK5) = sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5))
    | r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6323,c_2090,c_2988])).

cnf(c_6945,plain,
    ( sK2(sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK3,sK5) = sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_6940,c_6382])).

cnf(c_20,plain,
    ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ v4_lattice3(X1)
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_431,plain,
    ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
    | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
    | ~ l3_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_432,plain,
    ( m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
    | ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_436,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
    | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_30,c_29,c_27])).

cnf(c_437,plain,
    ( m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
    | ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1)) ),
    inference(renaming,[status(thm)],[c_436])).

cnf(c_2035,plain,
    ( m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3))
    | ~ r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) ),
    inference(subtyping,[status(esa)],[c_437])).

cnf(c_2460,plain,
    ( m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2035])).

cnf(c_12,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_742,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_743,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,X1),X1)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_747,plain,
    ( r2_hidden(sK1(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_743,c_27])).

cnf(c_748,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_747])).

cnf(c_2021,plain,
    ( r4_lattice3(sK3,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0_53,X0_54),X0_54) ),
    inference(subtyping,[status(esa)],[c_748])).

cnf(c_2473,plain,
    ( r4_lattice3(sK3,X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0_53,X0_54),X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_4227,plain,
    ( r4_lattice3(sK3,X0_53,sK4) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0_53,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2473,c_2459])).

cnf(c_13,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_721,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_722,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_721])).

cnf(c_726,plain,
    ( m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_27])).

cnf(c_727,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_726])).

cnf(c_2022,plain,
    ( r4_lattice3(sK3,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0_53,X0_54),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_727])).

cnf(c_2472,plain,
    ( r4_lattice3(sK3,X0_53,X0_54) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X0_53,X0_54),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2022])).

cnf(c_18,plain,
    ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_541,plain,
    ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
    | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_542,plain,
    ( r4_lattice3(sK3,sK2(X0,sK3,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_546,plain,
    ( ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
    | r4_lattice3(sK3,sK2(X0,sK3,X1),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_30,c_29,c_27])).

cnf(c_547,plain,
    ( r4_lattice3(sK3,sK2(X0,sK3,X1),X1)
    | ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1)) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_2029,plain,
    ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X0_54)
    | ~ r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) ),
    inference(subtyping,[status(esa)],[c_547])).

cnf(c_2465,plain,
    ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X0_54) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2029])).

cnf(c_14,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_694,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_695,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | r1_lattices(sK3,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_lattices(sK3,X2,X0)
    | ~ r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_27])).

cnf(c_700,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | r1_lattices(sK3,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X1) ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_2023,plain,
    ( ~ r4_lattice3(sK3,X0_53,X0_54)
    | r1_lattices(sK3,X1_53,X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
    | ~ r2_hidden(X1_53,X0_54) ),
    inference(subtyping,[status(esa)],[c_700])).

cnf(c_2471,plain,
    ( r4_lattice3(sK3,X0_53,X0_54) != iProver_top
    | r1_lattices(sK3,X1_53,X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1_53,X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2023])).

cnf(c_3903,plain,
    ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) != iProver_top
    | r1_lattices(sK3,X1_53,sK2(X0_53,sK3,X0_54)) = iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1_53,X1_54) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_2471])).

cnf(c_6313,plain,
    ( r1_lattices(sK3,X0_53,sK2(X1_53,sK3,X0_54)) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_53,X0_54) != iProver_top
    | r2_hidden(X1_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2465,c_3903])).

cnf(c_11,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_763,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_30])).

cnf(c_764,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_763])).

cnf(c_768,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_27])).

cnf(c_769,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_768])).

cnf(c_2020,plain,
    ( r4_lattice3(sK3,X0_53,X0_54)
    | ~ r1_lattices(sK3,sK1(sK3,X0_53,X0_54),X0_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_769])).

cnf(c_2474,plain,
    ( r4_lattice3(sK3,X0_53,X0_54) = iProver_top
    | r1_lattices(sK3,sK1(sK3,X0_53,X0_54),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2020])).

cnf(c_6442,plain,
    ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
    | r2_hidden(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_6313,c_2474])).

cnf(c_2057,plain,
    ( m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2035])).

cnf(c_7385,plain,
    ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
    | r2_hidden(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6442,c_2057])).

cnf(c_7389,plain,
    ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
    | r2_hidden(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2472,c_7385])).

cnf(c_7411,plain,
    ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
    | r2_hidden(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7389,c_2057])).

cnf(c_7417,plain,
    ( r4_lattice3(sK3,sK2(X0_53,sK3,sK5),sK4) = iProver_top
    | m1_subset_1(sK2(X0_53,sK3,sK5),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4227,c_7411])).

cnf(c_8113,plain,
    ( r4_lattice3(sK3,sK2(X0_53,sK3,sK5),sK4) = iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_7417])).

cnf(c_8120,plain,
    ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK4) = iProver_top
    | r2_hidden(sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),a_2_2_lattice3(sK3,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6945,c_8113])).

cnf(c_9230,plain,
    ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK4) = iProver_top
    | r3_lattice3(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) = iProver_top
    | m1_subset_1(k15_lattice3(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2477,c_8120])).

cnf(c_12923,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) = iProver_top
    | r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9230,c_2090])).

cnf(c_12924,plain,
    ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK4) = iProver_top
    | r3_lattice3(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12923])).

cnf(c_17,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_559,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X1,a_2_2_lattice3(X0,X2))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_560,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,a_2_2_lattice3(sK3,X1))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_564,plain,
    ( r2_hidden(X0,a_2_2_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_560,c_30,c_29,c_27])).

cnf(c_565,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,a_2_2_lattice3(sK3,X1)) ),
    inference(renaming,[status(thm)],[c_564])).

cnf(c_2028,plain,
    ( ~ r4_lattice3(sK3,X0_53,X0_54)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) ),
    inference(subtyping,[status(esa)],[c_565])).

cnf(c_2466,plain,
    ( r4_lattice3(sK3,X0_53,X0_54) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2028])).

cnf(c_6489,plain,
    ( r4_lattice3(sK3,sK0(sK3,k16_lattice3(sK3,a_2_2_lattice3(sK3,X0_54)),X1_54),X0_54) != iProver_top
    | r3_lattice3(sK3,k16_lattice3(sK3,a_2_2_lattice3(sK3,X0_54)),X1_54) = iProver_top
    | m1_subset_1(sK0(sK3,k16_lattice3(sK3,a_2_2_lattice3(sK3,X0_54)),X1_54),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2466,c_6482])).

cnf(c_6493,plain,
    ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top
    | r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6489,c_2030])).

cnf(c_2532,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54)
    | m1_subset_1(sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3))
    | ~ m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_2533,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) = iProver_top
    | m1_subset_1(sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2532])).

cnf(c_6523,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) = iProver_top
    | r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6493,c_2088,c_2533])).

cnf(c_6524,plain,
    ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top
    | r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_6523])).

cnf(c_12940,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12924,c_6524])).

cnf(c_2470,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2024])).

cnf(c_3751,plain,
    ( r1_lattices(sK3,k15_lattice3(sK3,X0_54),X0_53) = iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,X0_54),X0_53) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2470,c_2468])).

cnf(c_4363,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
    | r1_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
    | m1_subset_1(k16_lattice3(sK3,X1_54),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2462,c_3751])).

cnf(c_6178,plain,
    ( m1_subset_1(k16_lattice3(sK3,X1_54),u1_struct_0(sK3)) != iProver_top
    | r1_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
    | r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4363,c_2088])).

cnf(c_6179,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
    | r1_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
    | m1_subset_1(k16_lattice3(sK3,X1_54),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6178])).

cnf(c_5,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_383,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(resolution,[status(thm)],[c_1,c_5])).

cnf(c_387,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_3,c_2])).

cnf(c_606,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_387,c_29])).

cnf(c_607,plain,
    ( ~ r1_lattices(sK3,X0,X1)
    | r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ r1_lattices(sK3,X0,X1)
    | r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_30,c_27])).

cnf(c_612,plain,
    ( ~ r1_lattices(sK3,X0,X1)
    | r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_611])).

cnf(c_2027,plain,
    ( ~ r1_lattices(sK3,X0_53,X1_53)
    | r3_lattices(sK3,X0_53,X1_53)
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_612])).

cnf(c_2467,plain,
    ( r1_lattices(sK3,X0_53,X1_53) != iProver_top
    | r3_lattices(sK3,X0_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2027])).

cnf(c_3738,plain,
    ( r1_lattices(sK3,k15_lattice3(sK3,X0_54),X0_53) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,X0_54),X0_53) = iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2470,c_2467])).

cnf(c_6185,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
    | m1_subset_1(k16_lattice3(sK3,X1_54),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6179,c_3738])).

cnf(c_2591,plain,
    ( ~ r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54)
    | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54))
    | ~ m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2033])).

cnf(c_2592,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
    | m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2591])).

cnf(c_9410,plain,
    ( r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
    | r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6185,c_2088,c_2592])).

cnf(c_9411,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9410])).

cnf(c_9416,plain,
    ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),a_2_2_lattice3(sK3,X1_54)) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k15_lattice3(sK3,X1_54)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_9411])).

cnf(c_13137,plain,
    ( r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12940,c_9416])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13137,c_6490,c_2988,c_2827])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.84/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/1.00  
% 3.84/1.00  ------  iProver source info
% 3.84/1.00  
% 3.84/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.84/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/1.00  git: non_committed_changes: false
% 3.84/1.00  git: last_make_outside_of_git: false
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options
% 3.84/1.00  
% 3.84/1.00  --out_options                           all
% 3.84/1.00  --tptp_safe_out                         true
% 3.84/1.00  --problem_path                          ""
% 3.84/1.00  --include_path                          ""
% 3.84/1.00  --clausifier                            res/vclausify_rel
% 3.84/1.00  --clausifier_options                    ""
% 3.84/1.00  --stdin                                 false
% 3.84/1.00  --stats_out                             all
% 3.84/1.00  
% 3.84/1.00  ------ General Options
% 3.84/1.00  
% 3.84/1.00  --fof                                   false
% 3.84/1.00  --time_out_real                         305.
% 3.84/1.00  --time_out_virtual                      -1.
% 3.84/1.00  --symbol_type_check                     false
% 3.84/1.00  --clausify_out                          false
% 3.84/1.00  --sig_cnt_out                           false
% 3.84/1.00  --trig_cnt_out                          false
% 3.84/1.00  --trig_cnt_out_tolerance                1.
% 3.84/1.00  --trig_cnt_out_sk_spl                   false
% 3.84/1.00  --abstr_cl_out                          false
% 3.84/1.00  
% 3.84/1.00  ------ Global Options
% 3.84/1.00  
% 3.84/1.00  --schedule                              default
% 3.84/1.00  --add_important_lit                     false
% 3.84/1.00  --prop_solver_per_cl                    1000
% 3.84/1.00  --min_unsat_core                        false
% 3.84/1.00  --soft_assumptions                      false
% 3.84/1.00  --soft_lemma_size                       3
% 3.84/1.00  --prop_impl_unit_size                   0
% 3.84/1.00  --prop_impl_unit                        []
% 3.84/1.00  --share_sel_clauses                     true
% 3.84/1.00  --reset_solvers                         false
% 3.84/1.00  --bc_imp_inh                            [conj_cone]
% 3.84/1.00  --conj_cone_tolerance                   3.
% 3.84/1.00  --extra_neg_conj                        none
% 3.84/1.00  --large_theory_mode                     true
% 3.84/1.00  --prolific_symb_bound                   200
% 3.84/1.00  --lt_threshold                          2000
% 3.84/1.00  --clause_weak_htbl                      true
% 3.84/1.00  --gc_record_bc_elim                     false
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing Options
% 3.84/1.00  
% 3.84/1.00  --preprocessing_flag                    true
% 3.84/1.00  --time_out_prep_mult                    0.1
% 3.84/1.00  --splitting_mode                        input
% 3.84/1.00  --splitting_grd                         true
% 3.84/1.00  --splitting_cvd                         false
% 3.84/1.00  --splitting_cvd_svl                     false
% 3.84/1.00  --splitting_nvd                         32
% 3.84/1.00  --sub_typing                            true
% 3.84/1.00  --prep_gs_sim                           true
% 3.84/1.00  --prep_unflatten                        true
% 3.84/1.00  --prep_res_sim                          true
% 3.84/1.00  --prep_upred                            true
% 3.84/1.00  --prep_sem_filter                       exhaustive
% 3.84/1.00  --prep_sem_filter_out                   false
% 3.84/1.00  --pred_elim                             true
% 3.84/1.00  --res_sim_input                         true
% 3.84/1.00  --eq_ax_congr_red                       true
% 3.84/1.00  --pure_diseq_elim                       true
% 3.84/1.00  --brand_transform                       false
% 3.84/1.00  --non_eq_to_eq                          false
% 3.84/1.00  --prep_def_merge                        true
% 3.84/1.00  --prep_def_merge_prop_impl              false
% 3.84/1.00  --prep_def_merge_mbd                    true
% 3.84/1.00  --prep_def_merge_tr_red                 false
% 3.84/1.00  --prep_def_merge_tr_cl                  false
% 3.84/1.00  --smt_preprocessing                     true
% 3.84/1.00  --smt_ac_axioms                         fast
% 3.84/1.00  --preprocessed_out                      false
% 3.84/1.00  --preprocessed_stats                    false
% 3.84/1.00  
% 3.84/1.00  ------ Abstraction refinement Options
% 3.84/1.00  
% 3.84/1.00  --abstr_ref                             []
% 3.84/1.00  --abstr_ref_prep                        false
% 3.84/1.00  --abstr_ref_until_sat                   false
% 3.84/1.00  --abstr_ref_sig_restrict                funpre
% 3.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.00  --abstr_ref_under                       []
% 3.84/1.00  
% 3.84/1.00  ------ SAT Options
% 3.84/1.00  
% 3.84/1.00  --sat_mode                              false
% 3.84/1.00  --sat_fm_restart_options                ""
% 3.84/1.00  --sat_gr_def                            false
% 3.84/1.00  --sat_epr_types                         true
% 3.84/1.00  --sat_non_cyclic_types                  false
% 3.84/1.00  --sat_finite_models                     false
% 3.84/1.00  --sat_fm_lemmas                         false
% 3.84/1.00  --sat_fm_prep                           false
% 3.84/1.00  --sat_fm_uc_incr                        true
% 3.84/1.00  --sat_out_model                         small
% 3.84/1.00  --sat_out_clauses                       false
% 3.84/1.00  
% 3.84/1.00  ------ QBF Options
% 3.84/1.00  
% 3.84/1.00  --qbf_mode                              false
% 3.84/1.00  --qbf_elim_univ                         false
% 3.84/1.00  --qbf_dom_inst                          none
% 3.84/1.00  --qbf_dom_pre_inst                      false
% 3.84/1.00  --qbf_sk_in                             false
% 3.84/1.00  --qbf_pred_elim                         true
% 3.84/1.00  --qbf_split                             512
% 3.84/1.00  
% 3.84/1.00  ------ BMC1 Options
% 3.84/1.00  
% 3.84/1.00  --bmc1_incremental                      false
% 3.84/1.00  --bmc1_axioms                           reachable_all
% 3.84/1.00  --bmc1_min_bound                        0
% 3.84/1.00  --bmc1_max_bound                        -1
% 3.84/1.00  --bmc1_max_bound_default                -1
% 3.84/1.00  --bmc1_symbol_reachability              true
% 3.84/1.00  --bmc1_property_lemmas                  false
% 3.84/1.00  --bmc1_k_induction                      false
% 3.84/1.00  --bmc1_non_equiv_states                 false
% 3.84/1.00  --bmc1_deadlock                         false
% 3.84/1.00  --bmc1_ucm                              false
% 3.84/1.00  --bmc1_add_unsat_core                   none
% 3.84/1.00  --bmc1_unsat_core_children              false
% 3.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.00  --bmc1_out_stat                         full
% 3.84/1.00  --bmc1_ground_init                      false
% 3.84/1.00  --bmc1_pre_inst_next_state              false
% 3.84/1.00  --bmc1_pre_inst_state                   false
% 3.84/1.00  --bmc1_pre_inst_reach_state             false
% 3.84/1.00  --bmc1_out_unsat_core                   false
% 3.84/1.00  --bmc1_aig_witness_out                  false
% 3.84/1.00  --bmc1_verbose                          false
% 3.84/1.00  --bmc1_dump_clauses_tptp                false
% 3.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.00  --bmc1_dump_file                        -
% 3.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.00  --bmc1_ucm_extend_mode                  1
% 3.84/1.00  --bmc1_ucm_init_mode                    2
% 3.84/1.00  --bmc1_ucm_cone_mode                    none
% 3.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.00  --bmc1_ucm_relax_model                  4
% 3.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.00  --bmc1_ucm_layered_model                none
% 3.84/1.00  --bmc1_ucm_max_lemma_size               10
% 3.84/1.00  
% 3.84/1.00  ------ AIG Options
% 3.84/1.00  
% 3.84/1.00  --aig_mode                              false
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation Options
% 3.84/1.00  
% 3.84/1.00  --instantiation_flag                    true
% 3.84/1.00  --inst_sos_flag                         true
% 3.84/1.00  --inst_sos_phase                        true
% 3.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel_side                     num_symb
% 3.84/1.00  --inst_solver_per_active                1400
% 3.84/1.00  --inst_solver_calls_frac                1.
% 3.84/1.00  --inst_passive_queue_type               priority_queues
% 3.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.00  --inst_passive_queues_freq              [25;2]
% 3.84/1.00  --inst_dismatching                      true
% 3.84/1.00  --inst_eager_unprocessed_to_passive     true
% 3.84/1.00  --inst_prop_sim_given                   true
% 3.84/1.00  --inst_prop_sim_new                     false
% 3.84/1.00  --inst_subs_new                         false
% 3.84/1.00  --inst_eq_res_simp                      false
% 3.84/1.00  --inst_subs_given                       false
% 3.84/1.00  --inst_orphan_elimination               true
% 3.84/1.00  --inst_learning_loop_flag               true
% 3.84/1.00  --inst_learning_start                   3000
% 3.84/1.00  --inst_learning_factor                  2
% 3.84/1.00  --inst_start_prop_sim_after_learn       3
% 3.84/1.00  --inst_sel_renew                        solver
% 3.84/1.00  --inst_lit_activity_flag                true
% 3.84/1.00  --inst_restr_to_given                   false
% 3.84/1.00  --inst_activity_threshold               500
% 3.84/1.00  --inst_out_proof                        true
% 3.84/1.00  
% 3.84/1.00  ------ Resolution Options
% 3.84/1.00  
% 3.84/1.00  --resolution_flag                       true
% 3.84/1.00  --res_lit_sel                           adaptive
% 3.84/1.00  --res_lit_sel_side                      none
% 3.84/1.00  --res_ordering                          kbo
% 3.84/1.00  --res_to_prop_solver                    active
% 3.84/1.00  --res_prop_simpl_new                    false
% 3.84/1.00  --res_prop_simpl_given                  true
% 3.84/1.00  --res_passive_queue_type                priority_queues
% 3.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.00  --res_passive_queues_freq               [15;5]
% 3.84/1.00  --res_forward_subs                      full
% 3.84/1.00  --res_backward_subs                     full
% 3.84/1.00  --res_forward_subs_resolution           true
% 3.84/1.00  --res_backward_subs_resolution          true
% 3.84/1.00  --res_orphan_elimination                true
% 3.84/1.00  --res_time_limit                        2.
% 3.84/1.00  --res_out_proof                         true
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Options
% 3.84/1.00  
% 3.84/1.00  --superposition_flag                    true
% 3.84/1.00  --sup_passive_queue_type                priority_queues
% 3.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.00  --demod_completeness_check              fast
% 3.84/1.00  --demod_use_ground                      true
% 3.84/1.00  --sup_to_prop_solver                    passive
% 3.84/1.00  --sup_prop_simpl_new                    true
% 3.84/1.00  --sup_prop_simpl_given                  true
% 3.84/1.00  --sup_fun_splitting                     true
% 3.84/1.00  --sup_smt_interval                      50000
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Simplification Setup
% 3.84/1.00  
% 3.84/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/1.00  --sup_immed_triv                        [TrivRules]
% 3.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_bw_main                     []
% 3.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_input_bw                          []
% 3.84/1.00  
% 3.84/1.00  ------ Combination Options
% 3.84/1.00  
% 3.84/1.00  --comb_res_mult                         3
% 3.84/1.00  --comb_sup_mult                         2
% 3.84/1.00  --comb_inst_mult                        10
% 3.84/1.00  
% 3.84/1.00  ------ Debug Options
% 3.84/1.00  
% 3.84/1.00  --dbg_backtrace                         false
% 3.84/1.00  --dbg_dump_prop_clauses                 false
% 3.84/1.00  --dbg_dump_prop_clauses_file            -
% 3.84/1.00  --dbg_out_stat                          false
% 3.84/1.00  ------ Parsing...
% 3.84/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  ------ Proving...
% 3.84/1.00  ------ Problem Properties 
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  clauses                                 22
% 3.84/1.00  conjectures                             1
% 3.84/1.00  EPR                                     1
% 3.84/1.00  Horn                                    18
% 3.84/1.00  unary                                   3
% 3.84/1.00  binary                                  5
% 3.84/1.00  lits                                    61
% 3.84/1.00  lits eq                                 2
% 3.84/1.00  fd_pure                                 0
% 3.84/1.00  fd_pseudo                               0
% 3.84/1.00  fd_cond                                 0
% 3.84/1.00  fd_pseudo_cond                          0
% 3.84/1.00  AC symbols                              0
% 3.84/1.00  
% 3.84/1.00  ------ Schedule dynamic 5 is on 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  Current options:
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  ------ Input Options
% 3.84/1.00  
% 3.84/1.00  --out_options                           all
% 3.84/1.00  --tptp_safe_out                         true
% 3.84/1.00  --problem_path                          ""
% 3.84/1.00  --include_path                          ""
% 3.84/1.00  --clausifier                            res/vclausify_rel
% 3.84/1.00  --clausifier_options                    ""
% 3.84/1.00  --stdin                                 false
% 3.84/1.00  --stats_out                             all
% 3.84/1.00  
% 3.84/1.00  ------ General Options
% 3.84/1.00  
% 3.84/1.00  --fof                                   false
% 3.84/1.00  --time_out_real                         305.
% 3.84/1.00  --time_out_virtual                      -1.
% 3.84/1.00  --symbol_type_check                     false
% 3.84/1.00  --clausify_out                          false
% 3.84/1.00  --sig_cnt_out                           false
% 3.84/1.00  --trig_cnt_out                          false
% 3.84/1.00  --trig_cnt_out_tolerance                1.
% 3.84/1.00  --trig_cnt_out_sk_spl                   false
% 3.84/1.00  --abstr_cl_out                          false
% 3.84/1.00  
% 3.84/1.00  ------ Global Options
% 3.84/1.00  
% 3.84/1.00  --schedule                              default
% 3.84/1.00  --add_important_lit                     false
% 3.84/1.00  --prop_solver_per_cl                    1000
% 3.84/1.00  --min_unsat_core                        false
% 3.84/1.00  --soft_assumptions                      false
% 3.84/1.00  --soft_lemma_size                       3
% 3.84/1.00  --prop_impl_unit_size                   0
% 3.84/1.00  --prop_impl_unit                        []
% 3.84/1.00  --share_sel_clauses                     true
% 3.84/1.00  --reset_solvers                         false
% 3.84/1.00  --bc_imp_inh                            [conj_cone]
% 3.84/1.00  --conj_cone_tolerance                   3.
% 3.84/1.00  --extra_neg_conj                        none
% 3.84/1.00  --large_theory_mode                     true
% 3.84/1.00  --prolific_symb_bound                   200
% 3.84/1.00  --lt_threshold                          2000
% 3.84/1.00  --clause_weak_htbl                      true
% 3.84/1.00  --gc_record_bc_elim                     false
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing Options
% 3.84/1.00  
% 3.84/1.00  --preprocessing_flag                    true
% 3.84/1.00  --time_out_prep_mult                    0.1
% 3.84/1.00  --splitting_mode                        input
% 3.84/1.00  --splitting_grd                         true
% 3.84/1.00  --splitting_cvd                         false
% 3.84/1.00  --splitting_cvd_svl                     false
% 3.84/1.00  --splitting_nvd                         32
% 3.84/1.00  --sub_typing                            true
% 3.84/1.00  --prep_gs_sim                           true
% 3.84/1.00  --prep_unflatten                        true
% 3.84/1.00  --prep_res_sim                          true
% 3.84/1.00  --prep_upred                            true
% 3.84/1.00  --prep_sem_filter                       exhaustive
% 3.84/1.00  --prep_sem_filter_out                   false
% 3.84/1.00  --pred_elim                             true
% 3.84/1.00  --res_sim_input                         true
% 3.84/1.00  --eq_ax_congr_red                       true
% 3.84/1.00  --pure_diseq_elim                       true
% 3.84/1.00  --brand_transform                       false
% 3.84/1.00  --non_eq_to_eq                          false
% 3.84/1.00  --prep_def_merge                        true
% 3.84/1.00  --prep_def_merge_prop_impl              false
% 3.84/1.00  --prep_def_merge_mbd                    true
% 3.84/1.00  --prep_def_merge_tr_red                 false
% 3.84/1.00  --prep_def_merge_tr_cl                  false
% 3.84/1.00  --smt_preprocessing                     true
% 3.84/1.00  --smt_ac_axioms                         fast
% 3.84/1.00  --preprocessed_out                      false
% 3.84/1.00  --preprocessed_stats                    false
% 3.84/1.00  
% 3.84/1.00  ------ Abstraction refinement Options
% 3.84/1.00  
% 3.84/1.00  --abstr_ref                             []
% 3.84/1.00  --abstr_ref_prep                        false
% 3.84/1.00  --abstr_ref_until_sat                   false
% 3.84/1.00  --abstr_ref_sig_restrict                funpre
% 3.84/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/1.00  --abstr_ref_under                       []
% 3.84/1.00  
% 3.84/1.00  ------ SAT Options
% 3.84/1.00  
% 3.84/1.00  --sat_mode                              false
% 3.84/1.00  --sat_fm_restart_options                ""
% 3.84/1.00  --sat_gr_def                            false
% 3.84/1.00  --sat_epr_types                         true
% 3.84/1.00  --sat_non_cyclic_types                  false
% 3.84/1.00  --sat_finite_models                     false
% 3.84/1.00  --sat_fm_lemmas                         false
% 3.84/1.00  --sat_fm_prep                           false
% 3.84/1.00  --sat_fm_uc_incr                        true
% 3.84/1.00  --sat_out_model                         small
% 3.84/1.00  --sat_out_clauses                       false
% 3.84/1.00  
% 3.84/1.00  ------ QBF Options
% 3.84/1.00  
% 3.84/1.00  --qbf_mode                              false
% 3.84/1.00  --qbf_elim_univ                         false
% 3.84/1.00  --qbf_dom_inst                          none
% 3.84/1.00  --qbf_dom_pre_inst                      false
% 3.84/1.00  --qbf_sk_in                             false
% 3.84/1.00  --qbf_pred_elim                         true
% 3.84/1.00  --qbf_split                             512
% 3.84/1.00  
% 3.84/1.00  ------ BMC1 Options
% 3.84/1.00  
% 3.84/1.00  --bmc1_incremental                      false
% 3.84/1.00  --bmc1_axioms                           reachable_all
% 3.84/1.00  --bmc1_min_bound                        0
% 3.84/1.00  --bmc1_max_bound                        -1
% 3.84/1.00  --bmc1_max_bound_default                -1
% 3.84/1.00  --bmc1_symbol_reachability              true
% 3.84/1.00  --bmc1_property_lemmas                  false
% 3.84/1.00  --bmc1_k_induction                      false
% 3.84/1.00  --bmc1_non_equiv_states                 false
% 3.84/1.00  --bmc1_deadlock                         false
% 3.84/1.00  --bmc1_ucm                              false
% 3.84/1.00  --bmc1_add_unsat_core                   none
% 3.84/1.00  --bmc1_unsat_core_children              false
% 3.84/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/1.00  --bmc1_out_stat                         full
% 3.84/1.00  --bmc1_ground_init                      false
% 3.84/1.00  --bmc1_pre_inst_next_state              false
% 3.84/1.00  --bmc1_pre_inst_state                   false
% 3.84/1.00  --bmc1_pre_inst_reach_state             false
% 3.84/1.00  --bmc1_out_unsat_core                   false
% 3.84/1.00  --bmc1_aig_witness_out                  false
% 3.84/1.00  --bmc1_verbose                          false
% 3.84/1.00  --bmc1_dump_clauses_tptp                false
% 3.84/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.84/1.00  --bmc1_dump_file                        -
% 3.84/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.84/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.84/1.00  --bmc1_ucm_extend_mode                  1
% 3.84/1.00  --bmc1_ucm_init_mode                    2
% 3.84/1.00  --bmc1_ucm_cone_mode                    none
% 3.84/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.84/1.00  --bmc1_ucm_relax_model                  4
% 3.84/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.84/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/1.00  --bmc1_ucm_layered_model                none
% 3.84/1.00  --bmc1_ucm_max_lemma_size               10
% 3.84/1.00  
% 3.84/1.00  ------ AIG Options
% 3.84/1.00  
% 3.84/1.00  --aig_mode                              false
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation Options
% 3.84/1.00  
% 3.84/1.00  --instantiation_flag                    true
% 3.84/1.00  --inst_sos_flag                         true
% 3.84/1.00  --inst_sos_phase                        true
% 3.84/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/1.00  --inst_lit_sel_side                     none
% 3.84/1.00  --inst_solver_per_active                1400
% 3.84/1.00  --inst_solver_calls_frac                1.
% 3.84/1.00  --inst_passive_queue_type               priority_queues
% 3.84/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/1.00  --inst_passive_queues_freq              [25;2]
% 3.84/1.00  --inst_dismatching                      true
% 3.84/1.00  --inst_eager_unprocessed_to_passive     true
% 3.84/1.00  --inst_prop_sim_given                   true
% 3.84/1.00  --inst_prop_sim_new                     false
% 3.84/1.00  --inst_subs_new                         false
% 3.84/1.00  --inst_eq_res_simp                      false
% 3.84/1.00  --inst_subs_given                       false
% 3.84/1.00  --inst_orphan_elimination               true
% 3.84/1.00  --inst_learning_loop_flag               true
% 3.84/1.00  --inst_learning_start                   3000
% 3.84/1.00  --inst_learning_factor                  2
% 3.84/1.00  --inst_start_prop_sim_after_learn       3
% 3.84/1.00  --inst_sel_renew                        solver
% 3.84/1.00  --inst_lit_activity_flag                true
% 3.84/1.00  --inst_restr_to_given                   false
% 3.84/1.00  --inst_activity_threshold               500
% 3.84/1.00  --inst_out_proof                        true
% 3.84/1.00  
% 3.84/1.00  ------ Resolution Options
% 3.84/1.00  
% 3.84/1.00  --resolution_flag                       false
% 3.84/1.00  --res_lit_sel                           adaptive
% 3.84/1.00  --res_lit_sel_side                      none
% 3.84/1.00  --res_ordering                          kbo
% 3.84/1.00  --res_to_prop_solver                    active
% 3.84/1.00  --res_prop_simpl_new                    false
% 3.84/1.00  --res_prop_simpl_given                  true
% 3.84/1.00  --res_passive_queue_type                priority_queues
% 3.84/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/1.00  --res_passive_queues_freq               [15;5]
% 3.84/1.00  --res_forward_subs                      full
% 3.84/1.00  --res_backward_subs                     full
% 3.84/1.00  --res_forward_subs_resolution           true
% 3.84/1.00  --res_backward_subs_resolution          true
% 3.84/1.00  --res_orphan_elimination                true
% 3.84/1.00  --res_time_limit                        2.
% 3.84/1.00  --res_out_proof                         true
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Options
% 3.84/1.00  
% 3.84/1.00  --superposition_flag                    true
% 3.84/1.00  --sup_passive_queue_type                priority_queues
% 3.84/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.84/1.00  --demod_completeness_check              fast
% 3.84/1.00  --demod_use_ground                      true
% 3.84/1.00  --sup_to_prop_solver                    passive
% 3.84/1.00  --sup_prop_simpl_new                    true
% 3.84/1.00  --sup_prop_simpl_given                  true
% 3.84/1.00  --sup_fun_splitting                     true
% 3.84/1.00  --sup_smt_interval                      50000
% 3.84/1.00  
% 3.84/1.00  ------ Superposition Simplification Setup
% 3.84/1.00  
% 3.84/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/1.00  --sup_immed_triv                        [TrivRules]
% 3.84/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_immed_bw_main                     []
% 3.84/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/1.00  --sup_input_bw                          []
% 3.84/1.00  
% 3.84/1.00  ------ Combination Options
% 3.84/1.00  
% 3.84/1.00  --comb_res_mult                         3
% 3.84/1.00  --comb_sup_mult                         2
% 3.84/1.00  --comb_inst_mult                        10
% 3.84/1.00  
% 3.84/1.00  ------ Debug Options
% 3.84/1.00  
% 3.84/1.00  --dbg_backtrace                         false
% 3.84/1.00  --dbg_dump_prop_clauses                 false
% 3.84/1.00  --dbg_dump_prop_clauses_file            -
% 3.84/1.00  --dbg_out_stat                          false
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS status Theorem for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  fof(f4,axiom,(
% 3.84/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f23,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f4])).
% 3.84/1.00  
% 3.84/1.00  fof(f24,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(flattening,[],[f23])).
% 3.84/1.00  
% 3.84/1.00  fof(f42,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(nnf_transformation,[],[f24])).
% 3.84/1.00  
% 3.84/1.00  fof(f43,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(rectify,[],[f42])).
% 3.84/1.00  
% 3.84/1.00  fof(f44,plain,(
% 3.84/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f45,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.84/1.00  
% 3.84/1.00  fof(f66,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f45])).
% 3.84/1.00  
% 3.84/1.00  fof(f12,conjecture,(
% 3.84/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f13,negated_conjecture,(
% 3.84/1.00    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 3.84/1.00    inference(negated_conjecture,[],[f12])).
% 3.84/1.00  
% 3.84/1.00  fof(f39,plain,(
% 3.84/1.00    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f13])).
% 3.84/1.00  
% 3.84/1.00  fof(f40,plain,(
% 3.84/1.00    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.84/1.00    inference(flattening,[],[f39])).
% 3.84/1.00  
% 3.84/1.00  fof(f55,plain,(
% 3.84/1.00    ( ! [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK5),k16_lattice3(X0,sK4)) | ~r3_lattices(X0,k15_lattice3(X0,sK4),k15_lattice3(X0,sK5))) & r1_tarski(sK4,sK5))) )),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f54,plain,(
% 3.84/1.00    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : ((~r3_lattices(sK3,k16_lattice3(sK3,X2),k16_lattice3(sK3,X1)) | ~r3_lattices(sK3,k15_lattice3(sK3,X1),k15_lattice3(sK3,X2))) & r1_tarski(X1,X2)) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f56,plain,(
% 3.84/1.00    ((~r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4)) | ~r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5))) & r1_tarski(sK4,sK5)) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f55,f54])).
% 3.84/1.00  
% 3.84/1.00  fof(f82,plain,(
% 3.84/1.00    ~v2_struct_0(sK3)),
% 3.84/1.00    inference(cnf_transformation,[],[f56])).
% 3.84/1.00  
% 3.84/1.00  fof(f85,plain,(
% 3.84/1.00    l3_lattices(sK3)),
% 3.84/1.00    inference(cnf_transformation,[],[f56])).
% 3.84/1.00  
% 3.84/1.00  fof(f1,axiom,(
% 3.84/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f14,plain,(
% 3.84/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.84/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.84/1.00  
% 3.84/1.00  fof(f18,plain,(
% 3.84/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 3.84/1.00    inference(ennf_transformation,[],[f14])).
% 3.84/1.00  
% 3.84/1.00  fof(f57,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f18])).
% 3.84/1.00  
% 3.84/1.00  fof(f86,plain,(
% 3.84/1.00    r1_tarski(sK4,sK5)),
% 3.84/1.00    inference(cnf_transformation,[],[f56])).
% 3.84/1.00  
% 3.84/1.00  fof(f10,axiom,(
% 3.84/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f35,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f10])).
% 3.84/1.00  
% 3.84/1.00  fof(f36,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(flattening,[],[f35])).
% 3.84/1.00  
% 3.84/1.00  fof(f80,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f36])).
% 3.84/1.00  
% 3.84/1.00  fof(f84,plain,(
% 3.84/1.00    v4_lattice3(sK3)),
% 3.84/1.00    inference(cnf_transformation,[],[f56])).
% 3.84/1.00  
% 3.84/1.00  fof(f83,plain,(
% 3.84/1.00    v10_lattices(sK3)),
% 3.84/1.00    inference(cnf_transformation,[],[f56])).
% 3.84/1.00  
% 3.84/1.00  fof(f7,axiom,(
% 3.84/1.00    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f29,plain,(
% 3.84/1.00    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f7])).
% 3.84/1.00  
% 3.84/1.00  fof(f30,plain,(
% 3.84/1.00    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(flattening,[],[f29])).
% 3.84/1.00  
% 3.84/1.00  fof(f73,plain,(
% 3.84/1.00    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f30])).
% 3.84/1.00  
% 3.84/1.00  fof(f2,axiom,(
% 3.84/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f15,plain,(
% 3.84/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.84/1.00    inference(pure_predicate_removal,[],[f2])).
% 3.84/1.00  
% 3.84/1.00  fof(f16,plain,(
% 3.84/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.84/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.84/1.00  
% 3.84/1.00  fof(f17,plain,(
% 3.84/1.00    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 3.84/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.84/1.00  
% 3.84/1.00  fof(f19,plain,(
% 3.84/1.00    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.84/1.00    inference(ennf_transformation,[],[f17])).
% 3.84/1.00  
% 3.84/1.00  fof(f20,plain,(
% 3.84/1.00    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.84/1.00    inference(flattening,[],[f19])).
% 3.84/1.00  
% 3.84/1.00  fof(f61,plain,(
% 3.84/1.00    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f20])).
% 3.84/1.00  
% 3.84/1.00  fof(f3,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f21,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f3])).
% 3.84/1.00  
% 3.84/1.00  fof(f22,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(flattening,[],[f21])).
% 3.84/1.00  
% 3.84/1.00  fof(f41,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(nnf_transformation,[],[f22])).
% 3.84/1.00  
% 3.84/1.00  fof(f62,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f41])).
% 3.84/1.00  
% 3.84/1.00  fof(f59,plain,(
% 3.84/1.00    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f20])).
% 3.84/1.00  
% 3.84/1.00  fof(f60,plain,(
% 3.84/1.00    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f20])).
% 3.84/1.00  
% 3.84/1.00  fof(f67,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f45])).
% 3.84/1.00  
% 3.84/1.00  fof(f65,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f45])).
% 3.84/1.00  
% 3.84/1.00  fof(f8,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f31,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 3.84/1.00    inference(ennf_transformation,[],[f8])).
% 3.84/1.00  
% 3.84/1.00  fof(f32,plain,(
% 3.84/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.84/1.00    inference(flattening,[],[f31])).
% 3.84/1.00  
% 3.84/1.00  fof(f50,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.84/1.00    inference(nnf_transformation,[],[f32])).
% 3.84/1.00  
% 3.84/1.00  fof(f51,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.84/1.00    inference(rectify,[],[f50])).
% 3.84/1.00  
% 3.84/1.00  fof(f52,plain,(
% 3.84/1.00    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f53,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK2(X0,X1,X2),X2) & sK2(X0,X1,X2) = X0 & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 3.84/1.00  
% 3.84/1.00  fof(f75,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f53])).
% 3.84/1.00  
% 3.84/1.00  fof(f9,axiom,(
% 3.84/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f33,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f9])).
% 3.84/1.00  
% 3.84/1.00  fof(f34,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(flattening,[],[f33])).
% 3.84/1.00  
% 3.84/1.00  fof(f78,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f34])).
% 3.84/1.00  
% 3.84/1.00  fof(f11,axiom,(
% 3.84/1.00    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f37,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f11])).
% 3.84/1.00  
% 3.84/1.00  fof(f38,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(flattening,[],[f37])).
% 3.84/1.00  
% 3.84/1.00  fof(f81,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f38])).
% 3.84/1.00  
% 3.84/1.00  fof(f87,plain,(
% 3.84/1.00    ~r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4)) | ~r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5))),
% 3.84/1.00    inference(cnf_transformation,[],[f56])).
% 3.84/1.00  
% 3.84/1.00  fof(f6,axiom,(
% 3.84/1.00    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f27,plain,(
% 3.84/1.00    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f6])).
% 3.84/1.00  
% 3.84/1.00  fof(f28,plain,(
% 3.84/1.00    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(flattening,[],[f27])).
% 3.84/1.00  
% 3.84/1.00  fof(f72,plain,(
% 3.84/1.00    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f28])).
% 3.84/1.00  
% 3.84/1.00  fof(f74,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f53])).
% 3.84/1.00  
% 3.84/1.00  fof(f5,axiom,(
% 3.84/1.00    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f25,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f5])).
% 3.84/1.00  
% 3.84/1.00  fof(f26,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(flattening,[],[f25])).
% 3.84/1.00  
% 3.84/1.00  fof(f46,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(nnf_transformation,[],[f26])).
% 3.84/1.00  
% 3.84/1.00  fof(f47,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(rectify,[],[f46])).
% 3.84/1.00  
% 3.84/1.00  fof(f48,plain,(
% 3.84/1.00    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f49,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 3.84/1.00  
% 3.84/1.00  fof(f70,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f49])).
% 3.84/1.00  
% 3.84/1.00  fof(f69,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f49])).
% 3.84/1.00  
% 3.84/1.00  fof(f76,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK2(X0,X1,X2),X2) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f53])).
% 3.84/1.00  
% 3.84/1.00  fof(f68,plain,(
% 3.84/1.00    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f49])).
% 3.84/1.00  
% 3.84/1.00  fof(f71,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f49])).
% 3.84/1.00  
% 3.84/1.00  fof(f77,plain,(
% 3.84/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f53])).
% 3.84/1.00  
% 3.84/1.00  fof(f88,plain,(
% 3.84/1.00    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.84/1.00    inference(equality_resolution,[],[f77])).
% 3.84/1.00  
% 3.84/1.00  fof(f63,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f41])).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8,plain,
% 3.84/1.00      ( r3_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_30,negated_conjecture,
% 3.84/1.00      ( ~ v2_struct_0(sK3) ),
% 3.84/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_832,plain,
% 3.84/1.00      ( r3_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_833,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r2_hidden(sK0(sK3,X0,X1),X1)
% 3.84/1.00      | ~ l3_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_832]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_27,negated_conjecture,
% 3.84/1.00      ( l3_lattices(sK3) ),
% 3.84/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_837,plain,
% 3.84/1.00      ( r2_hidden(sK0(sK3,X0,X1),X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r3_lattice3(sK3,X0,X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_833,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_838,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r2_hidden(sK0(sK3,X0,X1),X1) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_837]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2017,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0_53,X0_54)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 3.84/1.00      | r2_hidden(sK0(sK3,X0_53,X0_54),X0_54) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_838]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2477,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0_53,X0_54) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(sK0(sK3,X0_53,X0_54),X0_54) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2017]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_0,plain,
% 3.84/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_26,negated_conjecture,
% 3.84/1.00      ( r1_tarski(sK4,sK5) ),
% 3.84/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_336,plain,
% 3.84/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK4 != X1 | sK5 != X2 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_26]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_337,plain,
% 3.84/1.00      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,sK5) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_336]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2036,plain,
% 3.84/1.00      ( ~ r2_hidden(X0_53,sK4) | r2_hidden(X0_53,sK5) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_337]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2459,plain,
% 3.84/1.00      ( r2_hidden(X0_53,sK4) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,sK5) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2036]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4244,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0_53,sK4) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(sK0(sK3,X0_53,sK4),sK5) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2477,c_2459]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_22,plain,
% 3.84/1.00      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ r2_hidden(X2,X1)
% 3.84/1.00      | ~ v4_lattice3(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_28,negated_conjecture,
% 3.84/1.00      ( v4_lattice3(sK3) ),
% 3.84/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_509,plain,
% 3.84/1.00      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ r2_hidden(X2,X1)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_510,plain,
% 3.84/1.00      ( r3_lattices(sK3,k16_lattice3(sK3,X0),X1)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.84/1.00      | ~ r2_hidden(X1,X0)
% 3.84/1.00      | ~ l3_lattices(sK3)
% 3.84/1.00      | v2_struct_0(sK3)
% 3.84/1.00      | ~ v10_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_509]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_29,negated_conjecture,
% 3.84/1.00      ( v10_lattices(sK3) ),
% 3.84/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_514,plain,
% 3.84/1.00      ( ~ r2_hidden(X1,X0)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.84/1.00      | r3_lattices(sK3,k16_lattice3(sK3,X0),X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_510,c_30,c_29,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_515,plain,
% 3.84/1.00      ( r3_lattices(sK3,k16_lattice3(sK3,X0),X1)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.84/1.00      | ~ r2_hidden(X1,X0) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_514]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2031,plain,
% 3.84/1.00      ( r3_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 3.84/1.00      | ~ r2_hidden(X0_53,X0_54) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_515]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2464,plain,
% 3.84/1.00      ( r3_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,X0_54) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2031]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_16,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_664,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_665,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
% 3.84/1.00      | ~ l3_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_664]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_669,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_665,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2025,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_669]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2469,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2025]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1,plain,
% 3.84/1.00      ( ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0)
% 3.84/1.00      | v9_lattices(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6,plain,
% 3.84/1.00      ( r1_lattices(X0,X1,X2)
% 3.84/1.00      | ~ r3_lattices(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ v6_lattices(X0)
% 3.84/1.00      | ~ v8_lattices(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v9_lattices(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_351,plain,
% 3.84/1.00      ( r1_lattices(X0,X1,X2)
% 3.84/1.00      | ~ r3_lattices(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ v6_lattices(X0)
% 3.84/1.00      | ~ v8_lattices(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(resolution,[status(thm)],[c_1,c_6]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3,plain,
% 3.84/1.00      ( v6_lattices(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2,plain,
% 3.84/1.00      ( v8_lattices(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_355,plain,
% 3.84/1.00      ( r1_lattices(X0,X1,X2)
% 3.84/1.00      | ~ r3_lattices(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_351,c_3,c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_630,plain,
% 3.84/1.00      ( r1_lattices(X0,X1,X2)
% 3.84/1.00      | ~ r3_lattices(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_355,c_29]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_631,plain,
% 3.84/1.00      ( r1_lattices(sK3,X0,X1)
% 3.84/1.00      | ~ r3_lattices(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.84/1.00      | ~ l3_lattices(sK3)
% 3.84/1.00      | v2_struct_0(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_630]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_635,plain,
% 3.84/1.00      ( r1_lattices(sK3,X0,X1)
% 3.84/1.00      | ~ r3_lattices(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_631,c_30,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_636,plain,
% 3.84/1.00      ( r1_lattices(sK3,X0,X1)
% 3.84/1.00      | ~ r3_lattices(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_635]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2026,plain,
% 3.84/1.00      ( r1_lattices(sK3,X0_53,X1_53)
% 3.84/1.00      | ~ r3_lattices(sK3,X0_53,X1_53)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_636]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2468,plain,
% 3.84/1.00      ( r1_lattices(sK3,X0_53,X1_53) = iProver_top
% 3.84/1.00      | r3_lattices(sK3,X0_53,X1_53) != iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2026]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3752,plain,
% 3.84/1.00      ( r1_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53) = iProver_top
% 3.84/1.00      | r3_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53) != iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2469,c_2468]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4697,plain,
% 3.84/1.00      ( r1_lattices(sK3,k16_lattice3(sK3,X0_54),X0_53) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,X0_54) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2464,c_3752]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7,plain,
% 3.84/1.00      ( r3_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_853,plain,
% 3.84/1.00      ( r3_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_854,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ l3_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_853]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_858,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
% 3.84/1.00      | r3_lattice3(sK3,X0,X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_854,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_859,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_858]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2016,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0_53,X0_54)
% 3.84/1.00      | ~ r1_lattices(sK3,X0_53,sK0(sK3,X0_53,X0_54))
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_859]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2478,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0_53,X0_54) = iProver_top
% 3.84/1.00      | r1_lattices(sK3,X0_53,sK0(sK3,X0_53,X0_54)) != iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2016]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4713,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4697,c_2478]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2085,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2025]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9,plain,
% 3.84/1.00      ( r3_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_811,plain,
% 3.84/1.00      ( r3_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_812,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
% 3.84/1.00      | ~ l3_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_811]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_816,plain,
% 3.84/1.00      ( m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r3_lattice3(sK3,X0,X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_812,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_817,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_816]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2018,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0_53,X0_54)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 3.84/1.00      | m1_subset_1(sK0(sK3,X0_53,X0_54),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_817]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2537,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_54),X1_54)
% 3.84/1.00      | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_2018]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2538,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3)) = iProver_top
% 3.84/1.00      | m1_subset_1(k16_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2537]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6482,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_4713,c_2085,c_2538]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6490,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) = iProver_top
% 3.84/1.00      | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4244,c_6482]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2987,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_2025]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2988,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2987]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6940,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) = iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_6490,c_2988]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_19,plain,
% 3.84/1.00      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.84/1.00      | ~ v4_lattice3(X1)
% 3.84/1.00      | ~ l3_lattices(X1)
% 3.84/1.00      | v2_struct_0(X1)
% 3.84/1.00      | ~ v10_lattices(X1)
% 3.84/1.00      | sK2(X0,X1,X2) = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_449,plain,
% 3.84/1.00      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.84/1.00      | ~ l3_lattices(X1)
% 3.84/1.00      | v2_struct_0(X1)
% 3.84/1.00      | ~ v10_lattices(X1)
% 3.84/1.00      | sK2(X0,X1,X2) = X0
% 3.84/1.00      | sK3 != X1 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_450,plain,
% 3.84/1.00      ( ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
% 3.84/1.00      | ~ l3_lattices(sK3)
% 3.84/1.00      | v2_struct_0(sK3)
% 3.84/1.00      | ~ v10_lattices(sK3)
% 3.84/1.00      | sK2(X0,sK3,X1) = X0 ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_449]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_454,plain,
% 3.84/1.00      ( ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1)) | sK2(X0,sK3,X1) = X0 ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_450,c_30,c_29,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2034,plain,
% 3.84/1.00      ( ~ r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54))
% 3.84/1.00      | sK2(X0_53,sK3,X0_54) = X0_53 ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_454]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2461,plain,
% 3.84/1.00      ( sK2(X0_53,sK3,X0_54) = X0_53
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2034]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4243,plain,
% 3.84/1.00      ( sK2(sK0(sK3,X0_53,a_2_2_lattice3(sK3,X0_54)),sK3,X0_54) = sK0(sK3,X0_53,a_2_2_lattice3(sK3,X0_54))
% 3.84/1.00      | r3_lattice3(sK3,X0_53,a_2_2_lattice3(sK3,X0_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2477,c_2461]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_21,plain,
% 3.84/1.00      ( ~ v4_lattice3(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0)
% 3.84/1.00      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_530,plain,
% 3.84/1.00      ( ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0)
% 3.84/1.00      | k16_lattice3(X0,a_2_2_lattice3(X0,X1)) = k15_lattice3(X0,X1)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_531,plain,
% 3.84/1.00      ( ~ l3_lattices(sK3)
% 3.84/1.00      | v2_struct_0(sK3)
% 3.84/1.00      | ~ v10_lattices(sK3)
% 3.84/1.00      | k16_lattice3(sK3,a_2_2_lattice3(sK3,X0)) = k15_lattice3(sK3,X0) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_530]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_535,plain,
% 3.84/1.00      ( k16_lattice3(sK3,a_2_2_lattice3(sK3,X0)) = k15_lattice3(sK3,X0) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_531,c_30,c_29,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2030,plain,
% 3.84/1.00      ( k16_lattice3(sK3,a_2_2_lattice3(sK3,X0_54)) = k15_lattice3(sK3,X0_54) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_535]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_24,plain,
% 3.84/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.84/1.00      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ v4_lattice3(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_467,plain,
% 3.84/1.00      ( ~ r3_lattice3(X0,X1,X2)
% 3.84/1.00      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_468,plain,
% 3.84/1.00      ( ~ r3_lattice3(sK3,X0,X1)
% 3.84/1.00      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ l3_lattices(sK3)
% 3.84/1.00      | v2_struct_0(sK3)
% 3.84/1.00      | ~ v10_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_467]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_472,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 3.84/1.00      | ~ r3_lattice3(sK3,X0,X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_468,c_30,c_29,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_473,plain,
% 3.84/1.00      ( ~ r3_lattice3(sK3,X0,X1)
% 3.84/1.00      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_472]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2033,plain,
% 3.84/1.00      ( ~ r3_lattice3(sK3,X0_53,X0_54)
% 3.84/1.00      | r3_lattices(sK3,X0_53,k16_lattice3(sK3,X0_54))
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_473]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2462,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0_53,X0_54) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,X0_53,k16_lattice3(sK3,X0_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2033]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2826,plain,
% 3.84/1.00      ( r3_lattice3(sK3,X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,X0_53,k15_lattice3(sK3,X0_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2030,c_2462]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5933,plain,
% 3.84/1.00      ( sK2(sK0(sK3,X0_53,a_2_2_lattice3(sK3,X0_54)),sK3,X0_54) = sK0(sK3,X0_53,a_2_2_lattice3(sK3,X0_54))
% 3.84/1.00      | r3_lattices(sK3,X0_53,k15_lattice3(sK3,X0_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4243,c_2826]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_25,negated_conjecture,
% 3.84/1.00      ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
% 3.84/1.00      | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2037,negated_conjecture,
% 3.84/1.00      ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
% 3.84/1.00      | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2458,plain,
% 3.84/1.00      ( r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4)) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2037]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2827,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top
% 3.84/1.00      | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2462,c_2458]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6323,plain,
% 3.84/1.00      ( sK2(sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK3,sK5) = sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5))
% 3.84/1.00      | r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) != iProver_top
% 3.84/1.00      | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | m1_subset_1(k15_lattice3(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5933,c_2827]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_15,plain,
% 3.84/1.00      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_679,plain,
% 3.84/1.00      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_680,plain,
% 3.84/1.00      ( m1_subset_1(k15_lattice3(sK3,X0),u1_struct_0(sK3))
% 3.84/1.00      | ~ l3_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_679]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_684,plain,
% 3.84/1.00      ( m1_subset_1(k15_lattice3(sK3,X0),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_680,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2024,plain,
% 3.84/1.00      ( m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_684]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2088,plain,
% 3.84/1.00      ( m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2024]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2090,plain,
% 3.84/1.00      ( m1_subset_1(k15_lattice3(sK3,sK4),u1_struct_0(sK3)) = iProver_top ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_2088]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6382,plain,
% 3.84/1.00      ( sK2(sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK3,sK5) = sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5))
% 3.84/1.00      | r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_6323,c_2090,c_2988]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6945,plain,
% 3.84/1.00      ( sK2(sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK3,sK5) = sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_6940,c_6382]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_20,plain,
% 3.84/1.00      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.84/1.00      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.84/1.00      | ~ v4_lattice3(X1)
% 3.84/1.00      | ~ l3_lattices(X1)
% 3.84/1.00      | v2_struct_0(X1)
% 3.84/1.00      | ~ v10_lattices(X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_431,plain,
% 3.84/1.00      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
% 3.84/1.00      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
% 3.84/1.00      | ~ l3_lattices(X1)
% 3.84/1.00      | v2_struct_0(X1)
% 3.84/1.00      | ~ v10_lattices(X1)
% 3.84/1.00      | sK3 != X1 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_432,plain,
% 3.84/1.00      ( m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
% 3.84/1.00      | ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
% 3.84/1.00      | ~ l3_lattices(sK3)
% 3.84/1.00      | v2_struct_0(sK3)
% 3.84/1.00      | ~ v10_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_431]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_436,plain,
% 3.84/1.00      ( ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
% 3.84/1.00      | m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_432,c_30,c_29,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_437,plain,
% 3.84/1.00      ( m1_subset_1(sK2(X0,sK3,X1),u1_struct_0(sK3))
% 3.84/1.00      | ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_436]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2035,plain,
% 3.84/1.00      ( m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3))
% 3.84/1.00      | ~ r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_437]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2460,plain,
% 3.84/1.00      ( m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3)) = iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2035]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12,plain,
% 3.84/1.00      ( r4_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_742,plain,
% 3.84/1.00      ( r4_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_743,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r2_hidden(sK1(sK3,X0,X1),X1)
% 3.84/1.00      | ~ l3_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_742]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_747,plain,
% 3.84/1.00      ( r2_hidden(sK1(sK3,X0,X1),X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r4_lattice3(sK3,X0,X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_743,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_748,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r2_hidden(sK1(sK3,X0,X1),X1) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_747]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2021,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0_53,X0_54)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 3.84/1.00      | r2_hidden(sK1(sK3,X0_53,X0_54),X0_54) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_748]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2473,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0_53,X0_54) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(sK1(sK3,X0_53,X0_54),X0_54) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4227,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0_53,sK4) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(sK1(sK3,X0_53,sK4),sK5) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2473,c_2459]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13,plain,
% 3.84/1.00      ( r4_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_721,plain,
% 3.84/1.00      ( r4_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_722,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
% 3.84/1.00      | ~ l3_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_721]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_726,plain,
% 3.84/1.00      ( m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r4_lattice3(sK3,X0,X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_722,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_727,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_726]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2022,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0_53,X0_54)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 3.84/1.00      | m1_subset_1(sK1(sK3,X0_53,X0_54),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_727]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2472,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0_53,X0_54) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | m1_subset_1(sK1(sK3,X0_53,X0_54),u1_struct_0(sK3)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2022]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18,plain,
% 3.84/1.00      ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.84/1.00      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.84/1.00      | ~ v4_lattice3(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_541,plain,
% 3.84/1.00      ( r4_lattice3(X0,sK2(X1,X0,X2),X2)
% 3.84/1.00      | ~ r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_542,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0,sK3,X1),X1)
% 3.84/1.00      | ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
% 3.84/1.00      | ~ l3_lattices(sK3)
% 3.84/1.00      | v2_struct_0(sK3)
% 3.84/1.00      | ~ v10_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_541]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_546,plain,
% 3.84/1.00      ( ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1))
% 3.84/1.00      | r4_lattice3(sK3,sK2(X0,sK3,X1),X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_542,c_30,c_29,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_547,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0,sK3,X1),X1)
% 3.84/1.00      | ~ r2_hidden(X0,a_2_2_lattice3(sK3,X1)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_546]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2029,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X0_54)
% 3.84/1.00      | ~ r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_547]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2465,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X0_54) = iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2029]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_14,plain,
% 3.84/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.00      | r1_lattices(X0,X3,X1)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.84/1.00      | ~ r2_hidden(X3,X2)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_694,plain,
% 3.84/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.00      | r1_lattices(X0,X3,X1)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.84/1.00      | ~ r2_hidden(X3,X2)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_695,plain,
% 3.84/1.00      ( ~ r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | r1_lattices(sK3,X2,X0)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 3.84/1.00      | ~ r2_hidden(X2,X1)
% 3.84/1.00      | ~ l3_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_694]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_699,plain,
% 3.84/1.00      ( ~ r2_hidden(X2,X1)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r1_lattices(sK3,X2,X0)
% 3.84/1.00      | ~ r4_lattice3(sK3,X0,X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_695,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_700,plain,
% 3.84/1.00      ( ~ r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | r1_lattices(sK3,X2,X0)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 3.84/1.00      | ~ r2_hidden(X2,X1) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_699]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2023,plain,
% 3.84/1.00      ( ~ r4_lattice3(sK3,X0_53,X0_54)
% 3.84/1.00      | r1_lattices(sK3,X1_53,X0_53)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3))
% 3.84/1.00      | ~ r2_hidden(X1_53,X0_54) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_700]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2471,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0_53,X0_54) != iProver_top
% 3.84/1.00      | r1_lattices(sK3,X1_53,X0_53) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X1_53,X0_54) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2023]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3903,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) != iProver_top
% 3.84/1.00      | r1_lattices(sK3,X1_53,sK2(X0_53,sK3,X0_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X1_53,X1_54) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2460,c_2471]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6313,plain,
% 3.84/1.00      ( r1_lattices(sK3,X0_53,sK2(X1_53,sK3,X0_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,X0_54) != iProver_top
% 3.84/1.00      | r2_hidden(X1_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2465,c_3903]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_11,plain,
% 3.84/1.00      ( r4_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_763,plain,
% 3.84/1.00      ( r4_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_764,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ l3_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_763]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_768,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
% 3.84/1.00      | r4_lattice3(sK3,X0,X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_764,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_769,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_768]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2020,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0_53,X0_54)
% 3.84/1.00      | ~ r1_lattices(sK3,sK1(sK3,X0_53,X0_54),X0_53)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_769]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2474,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0_53,X0_54) = iProver_top
% 3.84/1.00      | r1_lattices(sK3,sK1(sK3,X0_53,X0_54),X0_53) != iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2020]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6442,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | m1_subset_1(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
% 3.84/1.00      | r2_hidden(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),X0_54) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_6313,c_2474]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2057,plain,
% 3.84/1.00      ( m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3)) = iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2035]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7385,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | m1_subset_1(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
% 3.84/1.00      | r2_hidden(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),X0_54) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_6442,c_2057]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7389,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | m1_subset_1(sK2(X0_53,sK3,X0_54),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
% 3.84/1.00      | r2_hidden(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),X0_54) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2472,c_7385]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7411,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0_53,sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) != iProver_top
% 3.84/1.00      | r2_hidden(sK1(sK3,sK2(X0_53,sK3,X0_54),X1_54),X0_54) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_7389,c_2057]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7417,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0_53,sK3,sK5),sK4) = iProver_top
% 3.84/1.00      | m1_subset_1(sK2(X0_53,sK3,sK5),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,sK5)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4227,c_7411]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8113,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK2(X0_53,sK3,sK5),sK4) = iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,sK5)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2460,c_7417]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8120,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK4) = iProver_top
% 3.84/1.00      | r2_hidden(sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),a_2_2_lattice3(sK3,sK5)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_6945,c_8113]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9230,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK4) = iProver_top
% 3.84/1.00      | r3_lattice3(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) = iProver_top
% 3.84/1.00      | m1_subset_1(k15_lattice3(sK3,sK4),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2477,c_8120]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12923,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) = iProver_top
% 3.84/1.00      | r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK4) = iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_9230,c_2090]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12924,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)),sK4) = iProver_top
% 3.84/1.00      | r3_lattice3(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) = iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_12923]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_17,plain,
% 3.84/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.84/1.00      | ~ v4_lattice3(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_559,plain,
% 3.84/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | r2_hidden(X1,a_2_2_lattice3(X0,X2))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_560,plain,
% 3.84/1.00      ( ~ r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r2_hidden(X0,a_2_2_lattice3(sK3,X1))
% 3.84/1.00      | ~ l3_lattices(sK3)
% 3.84/1.00      | v2_struct_0(sK3)
% 3.84/1.00      | ~ v10_lattices(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_559]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_564,plain,
% 3.84/1.00      ( r2_hidden(X0,a_2_2_lattice3(sK3,X1))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ r4_lattice3(sK3,X0,X1) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_560,c_30,c_29,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_565,plain,
% 3.84/1.00      ( ~ r4_lattice3(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | r2_hidden(X0,a_2_2_lattice3(sK3,X1)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_564]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2028,plain,
% 3.84/1.00      ( ~ r4_lattice3(sK3,X0_53,X0_54)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_565]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2466,plain,
% 3.84/1.00      ( r4_lattice3(sK3,X0_53,X0_54) != iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r2_hidden(X0_53,a_2_2_lattice3(sK3,X0_54)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2028]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6489,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK0(sK3,k16_lattice3(sK3,a_2_2_lattice3(sK3,X0_54)),X1_54),X0_54) != iProver_top
% 3.84/1.00      | r3_lattice3(sK3,k16_lattice3(sK3,a_2_2_lattice3(sK3,X0_54)),X1_54) = iProver_top
% 3.84/1.00      | m1_subset_1(sK0(sK3,k16_lattice3(sK3,a_2_2_lattice3(sK3,X0_54)),X1_54),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2466,c_6482]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6493,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top
% 3.84/1.00      | r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | m1_subset_1(sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_6489,c_2030]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2532,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54)
% 3.84/1.00      | m1_subset_1(sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_2018]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2533,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | m1_subset_1(sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),u1_struct_0(sK3)) = iProver_top
% 3.84/1.00      | m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2532]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6523,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) = iProver_top
% 3.84/1.00      | r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_6493,c_2088,c_2533]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6524,plain,
% 3.84/1.00      ( r4_lattice3(sK3,sK0(sK3,k15_lattice3(sK3,X0_54),X1_54),X0_54) != iProver_top
% 3.84/1.00      | r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) = iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_6523]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12940,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,sK4),a_2_2_lattice3(sK3,sK5)) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_12924,c_6524]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2470,plain,
% 3.84/1.00      ( m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2024]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3751,plain,
% 3.84/1.00      ( r1_lattices(sK3,k15_lattice3(sK3,X0_54),X0_53) = iProver_top
% 3.84/1.00      | r3_lattices(sK3,k15_lattice3(sK3,X0_54),X0_53) != iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2470,c_2468]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4363,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
% 3.84/1.00      | r1_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(k16_lattice3(sK3,X1_54),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2462,c_3751]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6178,plain,
% 3.84/1.00      ( m1_subset_1(k16_lattice3(sK3,X1_54),u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | r1_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
% 3.84/1.00      | r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_4363,c_2088]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6179,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
% 3.84/1.00      | r1_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(k16_lattice3(sK3,X1_54),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_6178]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5,plain,
% 3.84/1.00      ( ~ r1_lattices(X0,X1,X2)
% 3.84/1.00      | r3_lattices(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ v6_lattices(X0)
% 3.84/1.00      | ~ v8_lattices(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v9_lattices(X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_383,plain,
% 3.84/1.00      ( ~ r1_lattices(X0,X1,X2)
% 3.84/1.00      | r3_lattices(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ v6_lattices(X0)
% 3.84/1.00      | ~ v8_lattices(X0)
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(resolution,[status(thm)],[c_1,c_5]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_387,plain,
% 3.84/1.00      ( ~ r1_lattices(X0,X1,X2)
% 3.84/1.00      | r3_lattices(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | ~ v10_lattices(X0) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_383,c_3,c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_606,plain,
% 3.84/1.00      ( ~ r1_lattices(X0,X1,X2)
% 3.84/1.00      | r3_lattices(X0,X1,X2)
% 3.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.84/1.00      | ~ l3_lattices(X0)
% 3.84/1.00      | v2_struct_0(X0)
% 3.84/1.00      | sK3 != X0 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_387,c_29]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_607,plain,
% 3.84/1.00      ( ~ r1_lattices(sK3,X0,X1)
% 3.84/1.00      | r3_lattices(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.84/1.00      | ~ l3_lattices(sK3)
% 3.84/1.00      | v2_struct_0(sK3) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_606]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_611,plain,
% 3.84/1.00      ( ~ r1_lattices(sK3,X0,X1)
% 3.84/1.00      | r3_lattices(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_607,c_30,c_27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_612,plain,
% 3.84/1.00      ( ~ r1_lattices(sK3,X0,X1)
% 3.84/1.00      | r3_lattices(sK3,X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_611]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2027,plain,
% 3.84/1.00      ( ~ r1_lattices(sK3,X0_53,X1_53)
% 3.84/1.00      | r3_lattices(sK3,X0_53,X1_53)
% 3.84/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 3.84/1.00      | ~ m1_subset_1(X1_53,u1_struct_0(sK3)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_612]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2467,plain,
% 3.84/1.00      ( r1_lattices(sK3,X0_53,X1_53) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,X0_53,X1_53) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 3.84/1.00      | m1_subset_1(X1_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2027]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3738,plain,
% 3.84/1.00      ( r1_lattices(sK3,k15_lattice3(sK3,X0_54),X0_53) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,k15_lattice3(sK3,X0_54),X0_53) = iProver_top
% 3.84/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2470,c_2467]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6185,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(k16_lattice3(sK3,X1_54),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_6179,c_3738]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2591,plain,
% 3.84/1.00      ( ~ r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54)
% 3.84/1.00      | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54))
% 3.84/1.00      | ~ m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_2033]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2592,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
% 3.84/1.00      | m1_subset_1(k15_lattice3(sK3,X0_54),u1_struct_0(sK3)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2591]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9410,plain,
% 3.84/1.00      ( r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top
% 3.84/1.00      | r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_6185,c_2088,c_2592]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9411,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),X1_54) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k16_lattice3(sK3,X1_54)) = iProver_top ),
% 3.84/1.00      inference(renaming,[status(thm)],[c_9410]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9416,plain,
% 3.84/1.00      ( r3_lattice3(sK3,k15_lattice3(sK3,X0_54),a_2_2_lattice3(sK3,X1_54)) != iProver_top
% 3.84/1.00      | r3_lattices(sK3,k15_lattice3(sK3,X0_54),k15_lattice3(sK3,X1_54)) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2030,c_9411]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13137,plain,
% 3.84/1.00      ( r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_12940,c_9416]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(contradiction,plain,
% 3.84/1.00      ( $false ),
% 3.84/1.00      inference(minisat,[status(thm)],[c_13137,c_6490,c_2988,c_2827]) ).
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  ------                               Statistics
% 3.84/1.00  
% 3.84/1.00  ------ General
% 3.84/1.00  
% 3.84/1.00  abstr_ref_over_cycles:                  0
% 3.84/1.00  abstr_ref_under_cycles:                 0
% 3.84/1.00  gc_basic_clause_elim:                   0
% 3.84/1.00  forced_gc_time:                         0
% 3.84/1.00  parsing_time:                           0.011
% 3.84/1.00  unif_index_cands_time:                  0.
% 3.84/1.00  unif_index_add_time:                    0.
% 3.84/1.00  orderings_time:                         0.
% 3.84/1.00  out_proof_time:                         0.018
% 3.84/1.00  total_time:                             0.45
% 3.84/1.00  num_of_symbols:                         56
% 3.84/1.00  num_of_terms:                           12796
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing
% 3.84/1.00  
% 3.84/1.00  num_of_splits:                          0
% 3.84/1.00  num_of_split_atoms:                     0
% 3.84/1.00  num_of_reused_defs:                     0
% 3.84/1.00  num_eq_ax_congr_red:                    56
% 3.84/1.00  num_of_sem_filtered_clauses:            1
% 3.84/1.00  num_of_subtypes:                        4
% 3.84/1.00  monotx_restored_types:                  1
% 3.84/1.00  sat_num_of_epr_types:                   0
% 3.84/1.00  sat_num_of_non_cyclic_types:            0
% 3.84/1.00  sat_guarded_non_collapsed_types:        0
% 3.84/1.00  num_pure_diseq_elim:                    0
% 3.84/1.00  simp_replaced_by:                       0
% 3.84/1.00  res_preprocessed:                       111
% 3.84/1.00  prep_upred:                             0
% 3.84/1.00  prep_unflattend:                        62
% 3.84/1.00  smt_new_axioms:                         0
% 3.84/1.00  pred_elim_cands:                        6
% 3.84/1.00  pred_elim:                              8
% 3.84/1.00  pred_elim_cl:                           8
% 3.84/1.00  pred_elim_cycles:                       14
% 3.84/1.00  merged_defs:                            0
% 3.84/1.00  merged_defs_ncl:                        0
% 3.84/1.00  bin_hyper_res:                          0
% 3.84/1.00  prep_cycles:                            4
% 3.84/1.00  pred_elim_time:                         0.041
% 3.84/1.00  splitting_time:                         0.
% 3.84/1.00  sem_filter_time:                        0.
% 3.84/1.00  monotx_time:                            0.
% 3.84/1.00  subtype_inf_time:                       0.001
% 3.84/1.00  
% 3.84/1.00  ------ Problem properties
% 3.84/1.00  
% 3.84/1.00  clauses:                                22
% 3.84/1.00  conjectures:                            1
% 3.84/1.00  epr:                                    1
% 3.84/1.00  horn:                                   18
% 3.84/1.00  ground:                                 1
% 3.84/1.00  unary:                                  3
% 3.84/1.00  binary:                                 5
% 3.84/1.00  lits:                                   61
% 3.84/1.00  lits_eq:                                2
% 3.84/1.00  fd_pure:                                0
% 3.84/1.00  fd_pseudo:                              0
% 3.84/1.00  fd_cond:                                0
% 3.84/1.00  fd_pseudo_cond:                         0
% 3.84/1.00  ac_symbols:                             0
% 3.84/1.00  
% 3.84/1.00  ------ Propositional Solver
% 3.84/1.00  
% 3.84/1.00  prop_solver_calls:                      30
% 3.84/1.00  prop_fast_solver_calls:                 1731
% 3.84/1.00  smt_solver_calls:                       0
% 3.84/1.00  smt_fast_solver_calls:                  0
% 3.84/1.00  prop_num_of_clauses:                    6645
% 3.84/1.00  prop_preprocess_simplified:             11906
% 3.84/1.00  prop_fo_subsumed:                       103
% 3.84/1.00  prop_solver_time:                       0.
% 3.84/1.00  smt_solver_time:                        0.
% 3.84/1.00  smt_fast_solver_time:                   0.
% 3.84/1.00  prop_fast_solver_time:                  0.
% 3.84/1.00  prop_unsat_core_time:                   0.
% 3.84/1.00  
% 3.84/1.00  ------ QBF
% 3.84/1.00  
% 3.84/1.00  qbf_q_res:                              0
% 3.84/1.00  qbf_num_tautologies:                    0
% 3.84/1.00  qbf_prep_cycles:                        0
% 3.84/1.00  
% 3.84/1.00  ------ BMC1
% 3.84/1.00  
% 3.84/1.00  bmc1_current_bound:                     -1
% 3.84/1.00  bmc1_last_solved_bound:                 -1
% 3.84/1.00  bmc1_unsat_core_size:                   -1
% 3.84/1.00  bmc1_unsat_core_parents_size:           -1
% 3.84/1.00  bmc1_merge_next_fun:                    0
% 3.84/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.84/1.00  
% 3.84/1.00  ------ Instantiation
% 3.84/1.00  
% 3.84/1.00  inst_num_of_clauses:                    1353
% 3.84/1.00  inst_num_in_passive:                    261
% 3.84/1.00  inst_num_in_active:                     597
% 3.84/1.00  inst_num_in_unprocessed:                495
% 3.84/1.00  inst_num_of_loops:                      780
% 3.84/1.00  inst_num_of_learning_restarts:          0
% 3.84/1.00  inst_num_moves_active_passive:          181
% 3.84/1.00  inst_lit_activity:                      0
% 3.84/1.00  inst_lit_activity_moves:                1
% 3.84/1.00  inst_num_tautologies:                   0
% 3.84/1.00  inst_num_prop_implied:                  0
% 3.84/1.00  inst_num_existing_simplified:           0
% 3.84/1.00  inst_num_eq_res_simplified:             0
% 3.84/1.00  inst_num_child_elim:                    0
% 3.84/1.00  inst_num_of_dismatching_blockings:      994
% 3.84/1.00  inst_num_of_non_proper_insts:           1390
% 3.84/1.00  inst_num_of_duplicates:                 0
% 3.84/1.00  inst_inst_num_from_inst_to_res:         0
% 3.84/1.00  inst_dismatching_checking_time:         0.
% 3.84/1.00  
% 3.84/1.00  ------ Resolution
% 3.84/1.00  
% 3.84/1.00  res_num_of_clauses:                     0
% 3.84/1.00  res_num_in_passive:                     0
% 3.84/1.00  res_num_in_active:                      0
% 3.84/1.00  res_num_of_loops:                       115
% 3.84/1.00  res_forward_subset_subsumed:            18
% 3.84/1.00  res_backward_subset_subsumed:           0
% 3.84/1.00  res_forward_subsumed:                   0
% 3.84/1.00  res_backward_subsumed:                  0
% 3.84/1.00  res_forward_subsumption_resolution:     3
% 3.84/1.00  res_backward_subsumption_resolution:    0
% 3.84/1.00  res_clause_to_clause_subsumption:       1483
% 3.84/1.00  res_orphan_elimination:                 0
% 3.84/1.00  res_tautology_del:                      55
% 3.84/1.00  res_num_eq_res_simplified:              0
% 3.84/1.00  res_num_sel_changes:                    0
% 3.84/1.00  res_moves_from_active_to_pass:          0
% 3.84/1.00  
% 3.84/1.00  ------ Superposition
% 3.84/1.00  
% 3.84/1.00  sup_time_total:                         0.
% 3.84/1.00  sup_time_generating:                    0.
% 3.84/1.00  sup_time_sim_full:                      0.
% 3.84/1.00  sup_time_sim_immed:                     0.
% 3.84/1.00  
% 3.84/1.00  sup_num_of_clauses:                     269
% 3.84/1.00  sup_num_in_active:                      131
% 3.84/1.00  sup_num_in_passive:                     138
% 3.84/1.00  sup_num_of_loops:                       154
% 3.84/1.00  sup_fw_superposition:                   208
% 3.84/1.00  sup_bw_superposition:                   156
% 3.84/1.00  sup_immediate_simplified:               81
% 3.84/1.00  sup_given_eliminated:                   8
% 3.84/1.00  comparisons_done:                       0
% 3.84/1.00  comparisons_avoided:                    9
% 3.84/1.00  
% 3.84/1.00  ------ Simplifications
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  sim_fw_subset_subsumed:                 16
% 3.84/1.00  sim_bw_subset_subsumed:                 9
% 3.84/1.00  sim_fw_subsumed:                        14
% 3.84/1.00  sim_bw_subsumed:                        25
% 3.84/1.00  sim_fw_subsumption_res:                 0
% 3.84/1.00  sim_bw_subsumption_res:                 0
% 3.84/1.00  sim_tautology_del:                      2
% 3.84/1.00  sim_eq_tautology_del:                   11
% 3.84/1.00  sim_eq_res_simp:                        0
% 3.84/1.00  sim_fw_demodulated:                     3
% 3.84/1.00  sim_bw_demodulated:                     0
% 3.84/1.00  sim_light_normalised:                   52
% 3.84/1.00  sim_joinable_taut:                      0
% 3.84/1.00  sim_joinable_simp:                      0
% 3.84/1.00  sim_ac_normalised:                      0
% 3.84/1.00  sim_smt_subsumption:                    0
% 3.84/1.00  
%------------------------------------------------------------------------------
