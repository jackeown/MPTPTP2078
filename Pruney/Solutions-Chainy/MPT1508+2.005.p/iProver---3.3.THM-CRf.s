%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:13 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 473 expanded)
%              Number of clauses        :   60 ( 104 expanded)
%              Number of leaves         :   12 ( 142 expanded)
%              Depth                    :   18
%              Number of atoms          :  630 (3245 expanded)
%              Number of equality atoms :   49 ( 384 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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

fof(f11,plain,(
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
    inference(pure_predicate_removal,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k16_lattice3(X0,X2) != X1
          & r3_lattice3(X0,X1,X2)
          & r2_hidden(X1,X2) )
     => ( k16_lattice3(X0,sK3) != X1
        & r3_lattice3(X0,X1,sK3)
        & r2_hidden(X1,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k16_lattice3(X0,X2) != sK2
            & r3_lattice3(X0,sK2,X2)
            & r2_hidden(sK2,X2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK1,X2) != X1
              & r3_lattice3(sK1,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v4_lattice3(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k16_lattice3(sK1,sK3) != sK2
    & r3_lattice3(sK1,sK2,sK3)
    & r2_hidden(sK2,sK3)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v4_lattice3(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f36,f35,f34])).

fof(f56,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK0(X0,X1,X2),X1)
        & r3_lattice3(X0,sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK0(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK0(X0,X1,X2),X2)
                  & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X4,X2,X0] :
      ( r3_lattices(X0,X4,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f57,plain,(
    v4_lattice3(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    k16_lattice3(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    r3_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v6_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v9_lattices(X0) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(resolution,[status(thm)],[c_0,c_7])).

cnf(c_2,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_406,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_2,c_1])).

cnf(c_23,negated_conjecture,
    ( v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_665,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_406,c_23])).

cnf(c_666,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_670,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_24,c_21])).

cnf(c_671,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ r3_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_670])).

cnf(c_1139,plain,
    ( r1_lattices(sK1,X0_50,X1_50)
    | ~ r3_lattices(sK1,X0_50,X1_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_671])).

cnf(c_1522,plain,
    ( r1_lattices(sK1,X0_50,k16_lattice3(sK1,X0_51))
    | ~ r3_lattices(sK1,X0_50,k16_lattice3(sK1,X0_51))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK1))
    | ~ m1_subset_1(k16_lattice3(sK1,X0_51),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_1524,plain,
    ( r1_lattices(sK1,sK2,k16_lattice3(sK1,sK3))
    | ~ r3_lattices(sK1,sK2,k16_lattice3(sK1,sK3))
    | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1522])).

cnf(c_3,plain,
    ( v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | ~ v4_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_264,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_5,c_8])).

cnf(c_302,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | X2 = X1 ),
    inference(resolution,[status(thm)],[c_3,c_264])).

cnf(c_689,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | X2 = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_302,c_23])).

cnf(c_690,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ r1_lattices(sK1,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_694,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ r1_lattices(sK1,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_690,c_24,c_21])).

cnf(c_695,plain,
    ( ~ r1_lattices(sK1,X0,X1)
    | ~ r1_lattices(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | X1 = X0 ),
    inference(renaming,[status(thm)],[c_694])).

cnf(c_1138,plain,
    ( ~ r1_lattices(sK1,X0_50,X1_50)
    | ~ r1_lattices(sK1,X1_50,X0_50)
    | ~ m1_subset_1(X0_50,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_50,u1_struct_0(sK1))
    | X1_50 = X0_50 ),
    inference(subtyping,[status(esa)],[c_695])).

cnf(c_1519,plain,
    ( ~ r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
    | ~ r1_lattices(sK1,sK2,k16_lattice3(sK1,sK3))
    | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k16_lattice3(sK1,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_1138])).

cnf(c_9,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_732,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_733,plain,
    ( m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1))
    | ~ l3_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_21])).

cnf(c_13,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( v4_lattice3(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_519,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_520,plain,
    ( ~ r3_lattice3(sK1,X0,X1)
    | r3_lattices(sK1,X0,k16_lattice3(sK1,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k16_lattice3(sK1,X1),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_524,plain,
    ( ~ m1_subset_1(k16_lattice3(sK1,X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r3_lattices(sK1,X0,k16_lattice3(sK1,X1))
    | ~ r3_lattice3(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_24,c_23,c_21])).

cnf(c_525,plain,
    ( ~ r3_lattice3(sK1,X0,X1)
    | r3_lattices(sK1,X0,k16_lattice3(sK1,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k16_lattice3(sK1,X1),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_524])).

cnf(c_748,plain,
    ( ~ r3_lattice3(sK1,X0,X1)
    | r3_lattices(sK1,X0,k16_lattice3(sK1,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_737,c_525])).

cnf(c_1136,plain,
    ( ~ r3_lattice3(sK1,X0_50,X0_51)
    | r3_lattices(sK1,X0_50,k16_lattice3(sK1,X0_51))
    | ~ m1_subset_1(X0_50,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_748])).

cnf(c_1188,plain,
    ( ~ r3_lattice3(sK1,sK2,sK3)
    | r3_lattices(sK1,sK2,k16_lattice3(sK1,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_1137,plain,
    ( m1_subset_1(k16_lattice3(sK1,X0_51),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_737])).

cnf(c_1185,plain,
    ( m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_17,negated_conjecture,
    ( k16_lattice3(sK1,sK3) != sK2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1149,negated_conjecture,
    ( k16_lattice3(sK1,sK3) != sK2 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_15,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_364,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_365,plain,
    ( r3_lattices(X0,k16_lattice3(X0,sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_482,plain,
    ( r3_lattices(X0,k16_lattice3(X0,sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_365,c_22])).

cnf(c_483,plain,
    ( r3_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_367,plain,
    ( r3_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattice3(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ v10_lattices(sK1) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_485,plain,
    ( r3_lattices(sK1,k16_lattice3(sK1,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_24,c_23,c_22,c_21,c_20,c_367])).

cnf(c_807,plain,
    ( r1_lattices(sK1,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k16_lattice3(sK1,sK3) != X0
    | sK2 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_485,c_671])).

cnf(c_808,plain,
    ( r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
    | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_810,plain,
    ( ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
    | r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_808,c_20])).

cnf(c_811,plain,
    ( r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
    | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_810])).

cnf(c_818,plain,
    ( r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_811,c_737])).

cnf(c_18,negated_conjecture,
    ( r3_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1524,c_1519,c_1188,c_1185,c_1149,c_818,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.09  % Command    : iproveropt_run.sh %d %s
% 0.09/0.30  % Computer   : n010.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.30  % DateTime   : Tue Dec  1 14:46:29 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.30  % Running in FOF mode
% 1.18/0.91  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.18/0.91  
% 1.18/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.18/0.91  
% 1.18/0.91  ------  iProver source info
% 1.18/0.91  
% 1.18/0.91  git: date: 2020-06-30 10:37:57 +0100
% 1.18/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.18/0.91  git: non_committed_changes: false
% 1.18/0.91  git: last_make_outside_of_git: false
% 1.18/0.91  
% 1.18/0.91  ------ 
% 1.18/0.91  
% 1.18/0.91  ------ Input Options
% 1.18/0.91  
% 1.18/0.91  --out_options                           all
% 1.18/0.91  --tptp_safe_out                         true
% 1.18/0.91  --problem_path                          ""
% 1.18/0.91  --include_path                          ""
% 1.18/0.91  --clausifier                            res/vclausify_rel
% 1.18/0.91  --clausifier_options                    --mode clausify
% 1.18/0.91  --stdin                                 false
% 1.18/0.91  --stats_out                             all
% 1.18/0.91  
% 1.18/0.91  ------ General Options
% 1.18/0.91  
% 1.18/0.91  --fof                                   false
% 1.18/0.91  --time_out_real                         305.
% 1.18/0.91  --time_out_virtual                      -1.
% 1.18/0.91  --symbol_type_check                     false
% 1.18/0.91  --clausify_out                          false
% 1.18/0.91  --sig_cnt_out                           false
% 1.18/0.91  --trig_cnt_out                          false
% 1.18/0.91  --trig_cnt_out_tolerance                1.
% 1.18/0.91  --trig_cnt_out_sk_spl                   false
% 1.18/0.91  --abstr_cl_out                          false
% 1.18/0.91  
% 1.18/0.91  ------ Global Options
% 1.18/0.91  
% 1.18/0.91  --schedule                              default
% 1.18/0.91  --add_important_lit                     false
% 1.18/0.91  --prop_solver_per_cl                    1000
% 1.18/0.91  --min_unsat_core                        false
% 1.18/0.91  --soft_assumptions                      false
% 1.18/0.91  --soft_lemma_size                       3
% 1.18/0.91  --prop_impl_unit_size                   0
% 1.18/0.91  --prop_impl_unit                        []
% 1.18/0.91  --share_sel_clauses                     true
% 1.18/0.91  --reset_solvers                         false
% 1.18/0.91  --bc_imp_inh                            [conj_cone]
% 1.18/0.91  --conj_cone_tolerance                   3.
% 1.18/0.91  --extra_neg_conj                        none
% 1.18/0.91  --large_theory_mode                     true
% 1.18/0.91  --prolific_symb_bound                   200
% 1.18/0.91  --lt_threshold                          2000
% 1.18/0.91  --clause_weak_htbl                      true
% 1.18/0.91  --gc_record_bc_elim                     false
% 1.18/0.91  
% 1.18/0.91  ------ Preprocessing Options
% 1.18/0.91  
% 1.18/0.91  --preprocessing_flag                    true
% 1.18/0.91  --time_out_prep_mult                    0.1
% 1.18/0.91  --splitting_mode                        input
% 1.18/0.91  --splitting_grd                         true
% 1.18/0.91  --splitting_cvd                         false
% 1.18/0.91  --splitting_cvd_svl                     false
% 1.18/0.91  --splitting_nvd                         32
% 1.18/0.91  --sub_typing                            true
% 1.18/0.91  --prep_gs_sim                           true
% 1.18/0.91  --prep_unflatten                        true
% 1.18/0.91  --prep_res_sim                          true
% 1.18/0.91  --prep_upred                            true
% 1.18/0.91  --prep_sem_filter                       exhaustive
% 1.18/0.91  --prep_sem_filter_out                   false
% 1.18/0.91  --pred_elim                             true
% 1.18/0.91  --res_sim_input                         true
% 1.18/0.91  --eq_ax_congr_red                       true
% 1.18/0.91  --pure_diseq_elim                       true
% 1.18/0.91  --brand_transform                       false
% 1.18/0.91  --non_eq_to_eq                          false
% 1.18/0.91  --prep_def_merge                        true
% 1.18/0.91  --prep_def_merge_prop_impl              false
% 1.18/0.91  --prep_def_merge_mbd                    true
% 1.18/0.91  --prep_def_merge_tr_red                 false
% 1.18/0.91  --prep_def_merge_tr_cl                  false
% 1.18/0.91  --smt_preprocessing                     true
% 1.18/0.91  --smt_ac_axioms                         fast
% 1.18/0.91  --preprocessed_out                      false
% 1.18/0.91  --preprocessed_stats                    false
% 1.18/0.91  
% 1.18/0.91  ------ Abstraction refinement Options
% 1.18/0.91  
% 1.18/0.91  --abstr_ref                             []
% 1.18/0.91  --abstr_ref_prep                        false
% 1.18/0.91  --abstr_ref_until_sat                   false
% 1.18/0.91  --abstr_ref_sig_restrict                funpre
% 1.18/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.91  --abstr_ref_under                       []
% 1.18/0.91  
% 1.18/0.91  ------ SAT Options
% 1.18/0.91  
% 1.18/0.91  --sat_mode                              false
% 1.18/0.91  --sat_fm_restart_options                ""
% 1.18/0.91  --sat_gr_def                            false
% 1.18/0.91  --sat_epr_types                         true
% 1.18/0.91  --sat_non_cyclic_types                  false
% 1.18/0.91  --sat_finite_models                     false
% 1.18/0.91  --sat_fm_lemmas                         false
% 1.18/0.91  --sat_fm_prep                           false
% 1.18/0.91  --sat_fm_uc_incr                        true
% 1.18/0.91  --sat_out_model                         small
% 1.18/0.91  --sat_out_clauses                       false
% 1.18/0.91  
% 1.18/0.91  ------ QBF Options
% 1.18/0.91  
% 1.18/0.91  --qbf_mode                              false
% 1.18/0.91  --qbf_elim_univ                         false
% 1.18/0.91  --qbf_dom_inst                          none
% 1.18/0.91  --qbf_dom_pre_inst                      false
% 1.18/0.91  --qbf_sk_in                             false
% 1.18/0.91  --qbf_pred_elim                         true
% 1.18/0.91  --qbf_split                             512
% 1.18/0.91  
% 1.18/0.91  ------ BMC1 Options
% 1.18/0.91  
% 1.18/0.91  --bmc1_incremental                      false
% 1.18/0.91  --bmc1_axioms                           reachable_all
% 1.18/0.91  --bmc1_min_bound                        0
% 1.18/0.91  --bmc1_max_bound                        -1
% 1.18/0.91  --bmc1_max_bound_default                -1
% 1.18/0.91  --bmc1_symbol_reachability              true
% 1.18/0.91  --bmc1_property_lemmas                  false
% 1.18/0.91  --bmc1_k_induction                      false
% 1.18/0.91  --bmc1_non_equiv_states                 false
% 1.18/0.91  --bmc1_deadlock                         false
% 1.18/0.91  --bmc1_ucm                              false
% 1.18/0.91  --bmc1_add_unsat_core                   none
% 1.18/0.91  --bmc1_unsat_core_children              false
% 1.18/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/0.91  --bmc1_out_stat                         full
% 1.18/0.91  --bmc1_ground_init                      false
% 1.18/0.91  --bmc1_pre_inst_next_state              false
% 1.18/0.91  --bmc1_pre_inst_state                   false
% 1.18/0.91  --bmc1_pre_inst_reach_state             false
% 1.18/0.91  --bmc1_out_unsat_core                   false
% 1.18/0.91  --bmc1_aig_witness_out                  false
% 1.18/0.91  --bmc1_verbose                          false
% 1.18/0.91  --bmc1_dump_clauses_tptp                false
% 1.18/0.91  --bmc1_dump_unsat_core_tptp             false
% 1.18/0.91  --bmc1_dump_file                        -
% 1.18/0.91  --bmc1_ucm_expand_uc_limit              128
% 1.18/0.91  --bmc1_ucm_n_expand_iterations          6
% 1.18/0.91  --bmc1_ucm_extend_mode                  1
% 1.18/0.91  --bmc1_ucm_init_mode                    2
% 1.18/0.91  --bmc1_ucm_cone_mode                    none
% 1.18/0.91  --bmc1_ucm_reduced_relation_type        0
% 1.18/0.91  --bmc1_ucm_relax_model                  4
% 1.18/0.91  --bmc1_ucm_full_tr_after_sat            true
% 1.18/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/0.91  --bmc1_ucm_layered_model                none
% 1.18/0.91  --bmc1_ucm_max_lemma_size               10
% 1.18/0.91  
% 1.18/0.91  ------ AIG Options
% 1.18/0.91  
% 1.18/0.91  --aig_mode                              false
% 1.18/0.91  
% 1.18/0.91  ------ Instantiation Options
% 1.18/0.91  
% 1.18/0.91  --instantiation_flag                    true
% 1.18/0.91  --inst_sos_flag                         false
% 1.18/0.91  --inst_sos_phase                        true
% 1.18/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/0.91  --inst_lit_sel_side                     num_symb
% 1.18/0.91  --inst_solver_per_active                1400
% 1.18/0.91  --inst_solver_calls_frac                1.
% 1.18/0.91  --inst_passive_queue_type               priority_queues
% 1.18/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/0.91  --inst_passive_queues_freq              [25;2]
% 1.18/0.91  --inst_dismatching                      true
% 1.18/0.91  --inst_eager_unprocessed_to_passive     true
% 1.18/0.91  --inst_prop_sim_given                   true
% 1.18/0.91  --inst_prop_sim_new                     false
% 1.18/0.91  --inst_subs_new                         false
% 1.18/0.91  --inst_eq_res_simp                      false
% 1.18/0.91  --inst_subs_given                       false
% 1.18/0.91  --inst_orphan_elimination               true
% 1.18/0.91  --inst_learning_loop_flag               true
% 1.18/0.91  --inst_learning_start                   3000
% 1.18/0.91  --inst_learning_factor                  2
% 1.18/0.91  --inst_start_prop_sim_after_learn       3
% 1.18/0.91  --inst_sel_renew                        solver
% 1.18/0.91  --inst_lit_activity_flag                true
% 1.18/0.91  --inst_restr_to_given                   false
% 1.18/0.91  --inst_activity_threshold               500
% 1.18/0.91  --inst_out_proof                        true
% 1.18/0.91  
% 1.18/0.91  ------ Resolution Options
% 1.18/0.91  
% 1.18/0.91  --resolution_flag                       true
% 1.18/0.91  --res_lit_sel                           adaptive
% 1.18/0.91  --res_lit_sel_side                      none
% 1.18/0.91  --res_ordering                          kbo
% 1.18/0.91  --res_to_prop_solver                    active
% 1.18/0.91  --res_prop_simpl_new                    false
% 1.18/0.91  --res_prop_simpl_given                  true
% 1.18/0.91  --res_passive_queue_type                priority_queues
% 1.18/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/0.91  --res_passive_queues_freq               [15;5]
% 1.18/0.91  --res_forward_subs                      full
% 1.18/0.91  --res_backward_subs                     full
% 1.18/0.91  --res_forward_subs_resolution           true
% 1.18/0.91  --res_backward_subs_resolution          true
% 1.18/0.91  --res_orphan_elimination                true
% 1.18/0.91  --res_time_limit                        2.
% 1.18/0.91  --res_out_proof                         true
% 1.18/0.91  
% 1.18/0.91  ------ Superposition Options
% 1.18/0.91  
% 1.18/0.91  --superposition_flag                    true
% 1.18/0.91  --sup_passive_queue_type                priority_queues
% 1.18/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/0.91  --sup_passive_queues_freq               [8;1;4]
% 1.18/0.91  --demod_completeness_check              fast
% 1.18/0.91  --demod_use_ground                      true
% 1.18/0.91  --sup_to_prop_solver                    passive
% 1.18/0.91  --sup_prop_simpl_new                    true
% 1.18/0.91  --sup_prop_simpl_given                  true
% 1.18/0.91  --sup_fun_splitting                     false
% 1.18/0.91  --sup_smt_interval                      50000
% 1.18/0.91  
% 1.18/0.91  ------ Superposition Simplification Setup
% 1.18/0.91  
% 1.18/0.91  --sup_indices_passive                   []
% 1.18/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.91  --sup_full_bw                           [BwDemod]
% 1.18/0.91  --sup_immed_triv                        [TrivRules]
% 1.18/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.91  --sup_immed_bw_main                     []
% 1.18/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.91  
% 1.18/0.91  ------ Combination Options
% 1.18/0.91  
% 1.18/0.91  --comb_res_mult                         3
% 1.18/0.91  --comb_sup_mult                         2
% 1.18/0.91  --comb_inst_mult                        10
% 1.18/0.91  
% 1.18/0.91  ------ Debug Options
% 1.18/0.91  
% 1.18/0.91  --dbg_backtrace                         false
% 1.18/0.91  --dbg_dump_prop_clauses                 false
% 1.18/0.91  --dbg_dump_prop_clauses_file            -
% 1.18/0.91  --dbg_out_stat                          false
% 1.18/0.91  ------ Parsing...
% 1.18/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.18/0.91  
% 1.18/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.18/0.91  
% 1.18/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.18/0.91  
% 1.18/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.18/0.91  ------ Proving...
% 1.18/0.91  ------ Problem Properties 
% 1.18/0.91  
% 1.18/0.91  
% 1.18/0.91  clauses                                 14
% 1.18/0.91  conjectures                             3
% 1.18/0.91  EPR                                     1
% 1.18/0.91  Horn                                    12
% 1.18/0.91  unary                                   7
% 1.18/0.91  binary                                  0
% 1.18/0.91  lits                                    35
% 1.18/0.91  lits eq                                 5
% 1.18/0.91  fd_pure                                 0
% 1.18/0.91  fd_pseudo                               0
% 1.18/0.91  fd_cond                                 0
% 1.18/0.91  fd_pseudo_cond                          4
% 1.18/0.91  AC symbols                              0
% 1.18/0.91  
% 1.18/0.91  ------ Schedule dynamic 5 is on 
% 1.18/0.91  
% 1.18/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.18/0.91  
% 1.18/0.91  
% 1.18/0.91  ------ 
% 1.18/0.91  Current options:
% 1.18/0.91  ------ 
% 1.18/0.91  
% 1.18/0.91  ------ Input Options
% 1.18/0.91  
% 1.18/0.91  --out_options                           all
% 1.18/0.91  --tptp_safe_out                         true
% 1.18/0.91  --problem_path                          ""
% 1.18/0.91  --include_path                          ""
% 1.18/0.91  --clausifier                            res/vclausify_rel
% 1.18/0.91  --clausifier_options                    --mode clausify
% 1.18/0.91  --stdin                                 false
% 1.18/0.91  --stats_out                             all
% 1.18/0.91  
% 1.18/0.91  ------ General Options
% 1.18/0.91  
% 1.18/0.91  --fof                                   false
% 1.18/0.91  --time_out_real                         305.
% 1.18/0.91  --time_out_virtual                      -1.
% 1.18/0.91  --symbol_type_check                     false
% 1.18/0.91  --clausify_out                          false
% 1.18/0.91  --sig_cnt_out                           false
% 1.18/0.91  --trig_cnt_out                          false
% 1.18/0.91  --trig_cnt_out_tolerance                1.
% 1.18/0.91  --trig_cnt_out_sk_spl                   false
% 1.18/0.91  --abstr_cl_out                          false
% 1.18/0.91  
% 1.18/0.91  ------ Global Options
% 1.18/0.91  
% 1.18/0.91  --schedule                              default
% 1.18/0.91  --add_important_lit                     false
% 1.18/0.91  --prop_solver_per_cl                    1000
% 1.18/0.91  --min_unsat_core                        false
% 1.18/0.91  --soft_assumptions                      false
% 1.18/0.91  --soft_lemma_size                       3
% 1.18/0.91  --prop_impl_unit_size                   0
% 1.18/0.91  --prop_impl_unit                        []
% 1.18/0.91  --share_sel_clauses                     true
% 1.18/0.91  --reset_solvers                         false
% 1.18/0.91  --bc_imp_inh                            [conj_cone]
% 1.18/0.91  --conj_cone_tolerance                   3.
% 1.18/0.91  --extra_neg_conj                        none
% 1.18/0.91  --large_theory_mode                     true
% 1.18/0.91  --prolific_symb_bound                   200
% 1.18/0.91  --lt_threshold                          2000
% 1.18/0.91  --clause_weak_htbl                      true
% 1.18/0.91  --gc_record_bc_elim                     false
% 1.18/0.91  
% 1.18/0.91  ------ Preprocessing Options
% 1.18/0.91  
% 1.18/0.91  --preprocessing_flag                    true
% 1.18/0.91  --time_out_prep_mult                    0.1
% 1.18/0.91  --splitting_mode                        input
% 1.18/0.91  --splitting_grd                         true
% 1.18/0.91  --splitting_cvd                         false
% 1.18/0.91  --splitting_cvd_svl                     false
% 1.18/0.91  --splitting_nvd                         32
% 1.18/0.91  --sub_typing                            true
% 1.18/0.91  --prep_gs_sim                           true
% 1.18/0.91  --prep_unflatten                        true
% 1.18/0.91  --prep_res_sim                          true
% 1.18/0.91  --prep_upred                            true
% 1.18/0.91  --prep_sem_filter                       exhaustive
% 1.18/0.91  --prep_sem_filter_out                   false
% 1.18/0.91  --pred_elim                             true
% 1.18/0.91  --res_sim_input                         true
% 1.18/0.91  --eq_ax_congr_red                       true
% 1.18/0.91  --pure_diseq_elim                       true
% 1.18/0.91  --brand_transform                       false
% 1.18/0.91  --non_eq_to_eq                          false
% 1.18/0.91  --prep_def_merge                        true
% 1.18/0.91  --prep_def_merge_prop_impl              false
% 1.18/0.91  --prep_def_merge_mbd                    true
% 1.18/0.91  --prep_def_merge_tr_red                 false
% 1.18/0.91  --prep_def_merge_tr_cl                  false
% 1.18/0.91  --smt_preprocessing                     true
% 1.18/0.91  --smt_ac_axioms                         fast
% 1.18/0.91  --preprocessed_out                      false
% 1.18/0.91  --preprocessed_stats                    false
% 1.18/0.91  
% 1.18/0.91  ------ Abstraction refinement Options
% 1.18/0.91  
% 1.18/0.91  --abstr_ref                             []
% 1.18/0.91  --abstr_ref_prep                        false
% 1.18/0.91  --abstr_ref_until_sat                   false
% 1.18/0.91  --abstr_ref_sig_restrict                funpre
% 1.18/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.91  --abstr_ref_under                       []
% 1.18/0.91  
% 1.18/0.91  ------ SAT Options
% 1.18/0.91  
% 1.18/0.91  --sat_mode                              false
% 1.18/0.91  --sat_fm_restart_options                ""
% 1.18/0.91  --sat_gr_def                            false
% 1.18/0.91  --sat_epr_types                         true
% 1.18/0.91  --sat_non_cyclic_types                  false
% 1.18/0.91  --sat_finite_models                     false
% 1.18/0.91  --sat_fm_lemmas                         false
% 1.18/0.91  --sat_fm_prep                           false
% 1.18/0.91  --sat_fm_uc_incr                        true
% 1.18/0.91  --sat_out_model                         small
% 1.18/0.91  --sat_out_clauses                       false
% 1.18/0.91  
% 1.18/0.91  ------ QBF Options
% 1.18/0.91  
% 1.18/0.91  --qbf_mode                              false
% 1.18/0.91  --qbf_elim_univ                         false
% 1.18/0.91  --qbf_dom_inst                          none
% 1.18/0.91  --qbf_dom_pre_inst                      false
% 1.18/0.91  --qbf_sk_in                             false
% 1.18/0.91  --qbf_pred_elim                         true
% 1.18/0.91  --qbf_split                             512
% 1.18/0.91  
% 1.18/0.91  ------ BMC1 Options
% 1.18/0.91  
% 1.18/0.91  --bmc1_incremental                      false
% 1.18/0.91  --bmc1_axioms                           reachable_all
% 1.18/0.91  --bmc1_min_bound                        0
% 1.18/0.91  --bmc1_max_bound                        -1
% 1.18/0.91  --bmc1_max_bound_default                -1
% 1.18/0.91  --bmc1_symbol_reachability              true
% 1.18/0.91  --bmc1_property_lemmas                  false
% 1.18/0.91  --bmc1_k_induction                      false
% 1.18/0.91  --bmc1_non_equiv_states                 false
% 1.18/0.91  --bmc1_deadlock                         false
% 1.18/0.91  --bmc1_ucm                              false
% 1.18/0.91  --bmc1_add_unsat_core                   none
% 1.18/0.91  --bmc1_unsat_core_children              false
% 1.18/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/0.91  --bmc1_out_stat                         full
% 1.18/0.91  --bmc1_ground_init                      false
% 1.18/0.91  --bmc1_pre_inst_next_state              false
% 1.18/0.91  --bmc1_pre_inst_state                   false
% 1.18/0.91  --bmc1_pre_inst_reach_state             false
% 1.18/0.91  --bmc1_out_unsat_core                   false
% 1.18/0.91  --bmc1_aig_witness_out                  false
% 1.18/0.91  --bmc1_verbose                          false
% 1.18/0.91  --bmc1_dump_clauses_tptp                false
% 1.18/0.91  --bmc1_dump_unsat_core_tptp             false
% 1.18/0.91  --bmc1_dump_file                        -
% 1.18/0.91  --bmc1_ucm_expand_uc_limit              128
% 1.18/0.91  --bmc1_ucm_n_expand_iterations          6
% 1.18/0.91  --bmc1_ucm_extend_mode                  1
% 1.18/0.91  --bmc1_ucm_init_mode                    2
% 1.18/0.91  --bmc1_ucm_cone_mode                    none
% 1.18/0.91  --bmc1_ucm_reduced_relation_type        0
% 1.18/0.91  --bmc1_ucm_relax_model                  4
% 1.18/0.91  --bmc1_ucm_full_tr_after_sat            true
% 1.18/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/0.91  --bmc1_ucm_layered_model                none
% 1.18/0.91  --bmc1_ucm_max_lemma_size               10
% 1.18/0.91  
% 1.18/0.91  ------ AIG Options
% 1.18/0.91  
% 1.18/0.91  --aig_mode                              false
% 1.18/0.91  
% 1.18/0.91  ------ Instantiation Options
% 1.18/0.91  
% 1.18/0.91  --instantiation_flag                    true
% 1.18/0.91  --inst_sos_flag                         false
% 1.18/0.91  --inst_sos_phase                        true
% 1.18/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/0.91  --inst_lit_sel_side                     none
% 1.18/0.91  --inst_solver_per_active                1400
% 1.18/0.91  --inst_solver_calls_frac                1.
% 1.18/0.91  --inst_passive_queue_type               priority_queues
% 1.18/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/0.91  --inst_passive_queues_freq              [25;2]
% 1.18/0.91  --inst_dismatching                      true
% 1.18/0.91  --inst_eager_unprocessed_to_passive     true
% 1.18/0.91  --inst_prop_sim_given                   true
% 1.18/0.91  --inst_prop_sim_new                     false
% 1.18/0.91  --inst_subs_new                         false
% 1.18/0.91  --inst_eq_res_simp                      false
% 1.18/0.91  --inst_subs_given                       false
% 1.18/0.91  --inst_orphan_elimination               true
% 1.18/0.91  --inst_learning_loop_flag               true
% 1.18/0.91  --inst_learning_start                   3000
% 1.18/0.91  --inst_learning_factor                  2
% 1.18/0.91  --inst_start_prop_sim_after_learn       3
% 1.18/0.91  --inst_sel_renew                        solver
% 1.18/0.91  --inst_lit_activity_flag                true
% 1.18/0.91  --inst_restr_to_given                   false
% 1.18/0.91  --inst_activity_threshold               500
% 1.18/0.91  --inst_out_proof                        true
% 1.18/0.91  
% 1.18/0.91  ------ Resolution Options
% 1.18/0.91  
% 1.18/0.91  --resolution_flag                       false
% 1.18/0.91  --res_lit_sel                           adaptive
% 1.18/0.91  --res_lit_sel_side                      none
% 1.18/0.91  --res_ordering                          kbo
% 1.18/0.91  --res_to_prop_solver                    active
% 1.18/0.91  --res_prop_simpl_new                    false
% 1.18/0.91  --res_prop_simpl_given                  true
% 1.18/0.91  --res_passive_queue_type                priority_queues
% 1.18/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/0.91  --res_passive_queues_freq               [15;5]
% 1.18/0.91  --res_forward_subs                      full
% 1.18/0.91  --res_backward_subs                     full
% 1.18/0.91  --res_forward_subs_resolution           true
% 1.18/0.91  --res_backward_subs_resolution          true
% 1.18/0.91  --res_orphan_elimination                true
% 1.18/0.91  --res_time_limit                        2.
% 1.18/0.91  --res_out_proof                         true
% 1.18/0.91  
% 1.18/0.91  ------ Superposition Options
% 1.18/0.91  
% 1.18/0.91  --superposition_flag                    true
% 1.18/0.91  --sup_passive_queue_type                priority_queues
% 1.18/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/0.91  --sup_passive_queues_freq               [8;1;4]
% 1.18/0.91  --demod_completeness_check              fast
% 1.18/0.91  --demod_use_ground                      true
% 1.18/0.91  --sup_to_prop_solver                    passive
% 1.18/0.91  --sup_prop_simpl_new                    true
% 1.18/0.91  --sup_prop_simpl_given                  true
% 1.18/0.91  --sup_fun_splitting                     false
% 1.18/0.91  --sup_smt_interval                      50000
% 1.18/0.91  
% 1.18/0.91  ------ Superposition Simplification Setup
% 1.18/0.91  
% 1.18/0.91  --sup_indices_passive                   []
% 1.18/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.91  --sup_full_bw                           [BwDemod]
% 1.18/0.91  --sup_immed_triv                        [TrivRules]
% 1.18/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.91  --sup_immed_bw_main                     []
% 1.18/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.91  
% 1.18/0.91  ------ Combination Options
% 1.18/0.91  
% 1.18/0.91  --comb_res_mult                         3
% 1.18/0.91  --comb_sup_mult                         2
% 1.18/0.91  --comb_inst_mult                        10
% 1.18/0.91  
% 1.18/0.91  ------ Debug Options
% 1.18/0.91  
% 1.18/0.91  --dbg_backtrace                         false
% 1.18/0.91  --dbg_dump_prop_clauses                 false
% 1.18/0.91  --dbg_dump_prop_clauses_file            -
% 1.18/0.91  --dbg_out_stat                          false
% 1.18/0.91  
% 1.18/0.91  
% 1.18/0.91  
% 1.18/0.91  
% 1.18/0.91  ------ Proving...
% 1.18/0.91  
% 1.18/0.91  
% 1.18/0.91  % SZS status Theorem for theBenchmark.p
% 1.18/0.91  
% 1.18/0.91  % SZS output start CNFRefutation for theBenchmark.p
% 1.18/0.91  
% 1.18/0.91  fof(f1,axiom,(
% 1.18/0.91    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.18/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.91  
% 1.18/0.91  fof(f11,plain,(
% 1.18/0.91    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.18/0.91    inference(pure_predicate_removal,[],[f1])).
% 1.18/0.91  
% 1.18/0.91  fof(f12,plain,(
% 1.18/0.91    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.18/0.91    inference(pure_predicate_removal,[],[f11])).
% 1.18/0.91  
% 1.18/0.91  fof(f13,plain,(
% 1.18/0.91    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.18/0.91    inference(ennf_transformation,[],[f12])).
% 1.18/0.91  
% 1.18/0.91  fof(f14,plain,(
% 1.18/0.91    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.18/0.91    inference(flattening,[],[f13])).
% 1.18/0.91  
% 1.18/0.91  fof(f42,plain,(
% 1.18/0.91    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f14])).
% 1.18/0.91  
% 1.18/0.91  fof(f3,axiom,(
% 1.18/0.91    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.18/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.91  
% 1.18/0.91  fof(f16,plain,(
% 1.18/0.91    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.91    inference(ennf_transformation,[],[f3])).
% 1.18/0.91  
% 1.18/0.91  fof(f17,plain,(
% 1.18/0.91    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(flattening,[],[f16])).
% 1.18/0.91  
% 1.18/0.91  fof(f28,plain,(
% 1.18/0.91    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(nnf_transformation,[],[f17])).
% 1.18/0.91  
% 1.18/0.91  fof(f44,plain,(
% 1.18/0.91    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f28])).
% 1.18/0.91  
% 1.18/0.91  fof(f40,plain,(
% 1.18/0.91    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f14])).
% 1.18/0.91  
% 1.18/0.91  fof(f41,plain,(
% 1.18/0.91    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f14])).
% 1.18/0.91  
% 1.18/0.91  fof(f8,conjecture,(
% 1.18/0.91    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.18/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.91  
% 1.18/0.91  fof(f9,negated_conjecture,(
% 1.18/0.91    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.18/0.91    inference(negated_conjecture,[],[f8])).
% 1.18/0.91  
% 1.18/0.91  fof(f26,plain,(
% 1.18/0.91    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.18/0.91    inference(ennf_transformation,[],[f9])).
% 1.18/0.91  
% 1.18/0.91  fof(f27,plain,(
% 1.18/0.91    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.18/0.91    inference(flattening,[],[f26])).
% 1.18/0.91  
% 1.18/0.91  fof(f36,plain,(
% 1.18/0.91    ( ! [X0,X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => (k16_lattice3(X0,sK3) != X1 & r3_lattice3(X0,X1,sK3) & r2_hidden(X1,sK3))) )),
% 1.18/0.91    introduced(choice_axiom,[])).
% 1.18/0.91  
% 1.18/0.91  fof(f35,plain,(
% 1.18/0.91    ( ! [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k16_lattice3(X0,X2) != sK2 & r3_lattice3(X0,sK2,X2) & r2_hidden(sK2,X2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.18/0.91    introduced(choice_axiom,[])).
% 1.18/0.91  
% 1.18/0.91  fof(f34,plain,(
% 1.18/0.91    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK1,X2) != X1 & r3_lattice3(sK1,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK1))) & l3_lattices(sK1) & v4_lattice3(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 1.18/0.91    introduced(choice_axiom,[])).
% 1.18/0.91  
% 1.18/0.91  fof(f37,plain,(
% 1.18/0.91    ((k16_lattice3(sK1,sK3) != sK2 & r3_lattice3(sK1,sK2,sK3) & r2_hidden(sK2,sK3)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v4_lattice3(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 1.18/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f36,f35,f34])).
% 1.18/0.91  
% 1.18/0.91  fof(f56,plain,(
% 1.18/0.91    v10_lattices(sK1)),
% 1.18/0.91    inference(cnf_transformation,[],[f37])).
% 1.18/0.91  
% 1.18/0.91  fof(f55,plain,(
% 1.18/0.91    ~v2_struct_0(sK1)),
% 1.18/0.91    inference(cnf_transformation,[],[f37])).
% 1.18/0.91  
% 1.18/0.91  fof(f58,plain,(
% 1.18/0.91    l3_lattices(sK1)),
% 1.18/0.91    inference(cnf_transformation,[],[f37])).
% 1.18/0.91  
% 1.18/0.91  fof(f39,plain,(
% 1.18/0.91    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f14])).
% 1.18/0.91  
% 1.18/0.91  fof(f2,axiom,(
% 1.18/0.91    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.18/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.91  
% 1.18/0.91  fof(f10,plain,(
% 1.18/0.91    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 1.18/0.91    inference(pure_predicate_removal,[],[f2])).
% 1.18/0.91  
% 1.18/0.91  fof(f15,plain,(
% 1.18/0.91    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 1.18/0.91    inference(ennf_transformation,[],[f10])).
% 1.18/0.91  
% 1.18/0.91  fof(f43,plain,(
% 1.18/0.91    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f15])).
% 1.18/0.91  
% 1.18/0.91  fof(f4,axiom,(
% 1.18/0.91    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 1.18/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.91  
% 1.18/0.91  fof(f18,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.91    inference(ennf_transformation,[],[f4])).
% 1.18/0.91  
% 1.18/0.91  fof(f19,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(flattening,[],[f18])).
% 1.18/0.91  
% 1.18/0.91  fof(f46,plain,(
% 1.18/0.91    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f19])).
% 1.18/0.91  
% 1.18/0.91  fof(f5,axiom,(
% 1.18/0.91    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.18/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.91  
% 1.18/0.91  fof(f20,plain,(
% 1.18/0.91    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.91    inference(ennf_transformation,[],[f5])).
% 1.18/0.91  
% 1.18/0.91  fof(f21,plain,(
% 1.18/0.91    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(flattening,[],[f20])).
% 1.18/0.91  
% 1.18/0.91  fof(f47,plain,(
% 1.18/0.91    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f21])).
% 1.18/0.91  
% 1.18/0.91  fof(f6,axiom,(
% 1.18/0.91    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.18/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.91  
% 1.18/0.91  fof(f22,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.91    inference(ennf_transformation,[],[f6])).
% 1.18/0.91  
% 1.18/0.91  fof(f23,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(flattening,[],[f22])).
% 1.18/0.91  
% 1.18/0.91  fof(f29,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(nnf_transformation,[],[f23])).
% 1.18/0.91  
% 1.18/0.91  fof(f30,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(flattening,[],[f29])).
% 1.18/0.91  
% 1.18/0.91  fof(f31,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(rectify,[],[f30])).
% 1.18/0.91  
% 1.18/0.91  fof(f32,plain,(
% 1.18/0.91    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK0(X0,X1,X2),X1) & r3_lattice3(X0,sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.18/0.91    introduced(choice_axiom,[])).
% 1.18/0.91  
% 1.18/0.91  fof(f33,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK0(X0,X1,X2),X1) & r3_lattice3(X0,sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 1.18/0.91  
% 1.18/0.91  fof(f49,plain,(
% 1.18/0.91    ( ! [X4,X2,X0,X1] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f33])).
% 1.18/0.91  
% 1.18/0.91  fof(f63,plain,(
% 1.18/0.91    ( ! [X4,X2,X0] : (r3_lattices(X0,X4,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.91    inference(equality_resolution,[],[f49])).
% 1.18/0.91  
% 1.18/0.91  fof(f57,plain,(
% 1.18/0.91    v4_lattice3(sK1)),
% 1.18/0.91    inference(cnf_transformation,[],[f37])).
% 1.18/0.91  
% 1.18/0.91  fof(f62,plain,(
% 1.18/0.91    k16_lattice3(sK1,sK3) != sK2),
% 1.18/0.91    inference(cnf_transformation,[],[f37])).
% 1.18/0.91  
% 1.18/0.91  fof(f7,axiom,(
% 1.18/0.91    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.18/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.91  
% 1.18/0.91  fof(f24,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.18/0.91    inference(ennf_transformation,[],[f7])).
% 1.18/0.91  
% 1.18/0.91  fof(f25,plain,(
% 1.18/0.91    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.18/0.91    inference(flattening,[],[f24])).
% 1.18/0.91  
% 1.18/0.91  fof(f54,plain,(
% 1.18/0.91    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.18/0.91    inference(cnf_transformation,[],[f25])).
% 1.18/0.91  
% 1.18/0.91  fof(f60,plain,(
% 1.18/0.91    r2_hidden(sK2,sK3)),
% 1.18/0.91    inference(cnf_transformation,[],[f37])).
% 1.18/0.91  
% 1.18/0.91  fof(f59,plain,(
% 1.18/0.91    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.18/0.91    inference(cnf_transformation,[],[f37])).
% 1.18/0.91  
% 1.18/0.91  fof(f61,plain,(
% 1.18/0.91    r3_lattice3(sK1,sK2,sK3)),
% 1.18/0.91    inference(cnf_transformation,[],[f37])).
% 1.18/0.91  
% 1.18/0.91  cnf(c_0,plain,
% 1.18/0.91      ( ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0)
% 1.18/0.91      | v9_lattices(X0) ),
% 1.18/0.91      inference(cnf_transformation,[],[f42]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_7,plain,
% 1.18/0.91      ( r1_lattices(X0,X1,X2)
% 1.18/0.91      | ~ r3_lattices(X0,X1,X2)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ v6_lattices(X0)
% 1.18/0.91      | ~ v8_lattices(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v9_lattices(X0) ),
% 1.18/0.91      inference(cnf_transformation,[],[f44]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_402,plain,
% 1.18/0.91      ( r1_lattices(X0,X1,X2)
% 1.18/0.91      | ~ r3_lattices(X0,X1,X2)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ v6_lattices(X0)
% 1.18/0.91      | ~ v8_lattices(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0) ),
% 1.18/0.91      inference(resolution,[status(thm)],[c_0,c_7]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_2,plain,
% 1.18/0.91      ( v6_lattices(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0) ),
% 1.18/0.91      inference(cnf_transformation,[],[f40]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1,plain,
% 1.18/0.91      ( v8_lattices(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0) ),
% 1.18/0.91      inference(cnf_transformation,[],[f41]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_406,plain,
% 1.18/0.91      ( r1_lattices(X0,X1,X2)
% 1.18/0.91      | ~ r3_lattices(X0,X1,X2)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0) ),
% 1.18/0.91      inference(global_propositional_subsumption,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_402,c_2,c_1]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_23,negated_conjecture,
% 1.18/0.91      ( v10_lattices(sK1) ),
% 1.18/0.91      inference(cnf_transformation,[],[f56]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_665,plain,
% 1.18/0.91      ( r1_lattices(X0,X1,X2)
% 1.18/0.91      | ~ r3_lattices(X0,X1,X2)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | sK1 != X0 ),
% 1.18/0.91      inference(resolution_lifted,[status(thm)],[c_406,c_23]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_666,plain,
% 1.18/0.91      ( r1_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ r3_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.18/0.91      | ~ l3_lattices(sK1)
% 1.18/0.91      | v2_struct_0(sK1) ),
% 1.18/0.91      inference(unflattening,[status(thm)],[c_665]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_24,negated_conjecture,
% 1.18/0.91      ( ~ v2_struct_0(sK1) ),
% 1.18/0.91      inference(cnf_transformation,[],[f55]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_21,negated_conjecture,
% 1.18/0.91      ( l3_lattices(sK1) ),
% 1.18/0.91      inference(cnf_transformation,[],[f58]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_670,plain,
% 1.18/0.91      ( r1_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ r3_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.18/0.91      inference(global_propositional_subsumption,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_666,c_24,c_21]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_671,plain,
% 1.18/0.91      ( r1_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ r3_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.18/0.91      inference(renaming,[status(thm)],[c_670]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1139,plain,
% 1.18/0.91      ( r1_lattices(sK1,X0_50,X1_50)
% 1.18/0.91      | ~ r3_lattices(sK1,X0_50,X1_50)
% 1.18/0.91      | ~ m1_subset_1(X0_50,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X1_50,u1_struct_0(sK1)) ),
% 1.18/0.91      inference(subtyping,[status(esa)],[c_671]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1522,plain,
% 1.18/0.91      ( r1_lattices(sK1,X0_50,k16_lattice3(sK1,X0_51))
% 1.18/0.91      | ~ r3_lattices(sK1,X0_50,k16_lattice3(sK1,X0_51))
% 1.18/0.91      | ~ m1_subset_1(X0_50,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(k16_lattice3(sK1,X0_51),u1_struct_0(sK1)) ),
% 1.18/0.91      inference(instantiation,[status(thm)],[c_1139]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1524,plain,
% 1.18/0.91      ( r1_lattices(sK1,sK2,k16_lattice3(sK1,sK3))
% 1.18/0.91      | ~ r3_lattices(sK1,sK2,k16_lattice3(sK1,sK3))
% 1.18/0.91      | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.18/0.91      inference(instantiation,[status(thm)],[c_1522]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_3,plain,
% 1.18/0.91      ( v4_lattices(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0) ),
% 1.18/0.91      inference(cnf_transformation,[],[f39]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_5,plain,
% 1.18/0.91      ( l2_lattices(X0) | ~ l3_lattices(X0) ),
% 1.18/0.91      inference(cnf_transformation,[],[f43]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_8,plain,
% 1.18/0.91      ( ~ r1_lattices(X0,X1,X2)
% 1.18/0.91      | ~ r1_lattices(X0,X2,X1)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ l2_lattices(X0)
% 1.18/0.91      | ~ v4_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | X2 = X1 ),
% 1.18/0.91      inference(cnf_transformation,[],[f46]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_264,plain,
% 1.18/0.91      ( ~ r1_lattices(X0,X1,X2)
% 1.18/0.91      | ~ r1_lattices(X0,X2,X1)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ v4_lattices(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | X2 = X1 ),
% 1.18/0.91      inference(resolution,[status(thm)],[c_5,c_8]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_302,plain,
% 1.18/0.91      ( ~ r1_lattices(X0,X1,X2)
% 1.18/0.91      | ~ r1_lattices(X0,X2,X1)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0)
% 1.18/0.91      | X2 = X1 ),
% 1.18/0.91      inference(resolution,[status(thm)],[c_3,c_264]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_689,plain,
% 1.18/0.91      ( ~ r1_lattices(X0,X1,X2)
% 1.18/0.91      | ~ r1_lattices(X0,X2,X1)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | X2 = X1
% 1.18/0.91      | sK1 != X0 ),
% 1.18/0.91      inference(resolution_lifted,[status(thm)],[c_302,c_23]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_690,plain,
% 1.18/0.91      ( ~ r1_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ r1_lattices(sK1,X1,X0)
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.18/0.91      | ~ l3_lattices(sK1)
% 1.18/0.91      | v2_struct_0(sK1)
% 1.18/0.91      | X1 = X0 ),
% 1.18/0.91      inference(unflattening,[status(thm)],[c_689]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_694,plain,
% 1.18/0.91      ( ~ r1_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ r1_lattices(sK1,X1,X0)
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.18/0.91      | X1 = X0 ),
% 1.18/0.91      inference(global_propositional_subsumption,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_690,c_24,c_21]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_695,plain,
% 1.18/0.91      ( ~ r1_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ r1_lattices(sK1,X1,X0)
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.18/0.91      | X1 = X0 ),
% 1.18/0.91      inference(renaming,[status(thm)],[c_694]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1138,plain,
% 1.18/0.91      ( ~ r1_lattices(sK1,X0_50,X1_50)
% 1.18/0.91      | ~ r1_lattices(sK1,X1_50,X0_50)
% 1.18/0.91      | ~ m1_subset_1(X0_50,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X1_50,u1_struct_0(sK1))
% 1.18/0.91      | X1_50 = X0_50 ),
% 1.18/0.91      inference(subtyping,[status(esa)],[c_695]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1519,plain,
% 1.18/0.91      ( ~ r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
% 1.18/0.91      | ~ r1_lattices(sK1,sK2,k16_lattice3(sK1,sK3))
% 1.18/0.91      | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.18/0.91      | k16_lattice3(sK1,sK3) = sK2 ),
% 1.18/0.91      inference(instantiation,[status(thm)],[c_1138]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_9,plain,
% 1.18/0.91      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0) ),
% 1.18/0.91      inference(cnf_transformation,[],[f47]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_732,plain,
% 1.18/0.91      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | sK1 != X0 ),
% 1.18/0.91      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_733,plain,
% 1.18/0.91      ( m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1))
% 1.18/0.91      | ~ l3_lattices(sK1) ),
% 1.18/0.91      inference(unflattening,[status(thm)],[c_732]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_737,plain,
% 1.18/0.91      ( m1_subset_1(k16_lattice3(sK1,X0),u1_struct_0(sK1)) ),
% 1.18/0.91      inference(global_propositional_subsumption,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_733,c_21]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_13,plain,
% 1.18/0.91      ( ~ r3_lattice3(X0,X1,X2)
% 1.18/0.91      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 1.18/0.91      | ~ v4_lattice3(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0) ),
% 1.18/0.91      inference(cnf_transformation,[],[f63]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_22,negated_conjecture,
% 1.18/0.91      ( v4_lattice3(sK1) ),
% 1.18/0.91      inference(cnf_transformation,[],[f57]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_519,plain,
% 1.18/0.91      ( ~ r3_lattice3(X0,X1,X2)
% 1.18/0.91      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.18/0.91      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0)
% 1.18/0.91      | sK1 != X0 ),
% 1.18/0.91      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_520,plain,
% 1.18/0.91      ( ~ r3_lattice3(sK1,X0,X1)
% 1.18/0.91      | r3_lattices(sK1,X0,k16_lattice3(sK1,X1))
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(k16_lattice3(sK1,X1),u1_struct_0(sK1))
% 1.18/0.91      | ~ l3_lattices(sK1)
% 1.18/0.91      | v2_struct_0(sK1)
% 1.18/0.91      | ~ v10_lattices(sK1) ),
% 1.18/0.91      inference(unflattening,[status(thm)],[c_519]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_524,plain,
% 1.18/0.91      ( ~ m1_subset_1(k16_lattice3(sK1,X1),u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.18/0.91      | r3_lattices(sK1,X0,k16_lattice3(sK1,X1))
% 1.18/0.91      | ~ r3_lattice3(sK1,X0,X1) ),
% 1.18/0.91      inference(global_propositional_subsumption,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_520,c_24,c_23,c_21]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_525,plain,
% 1.18/0.91      ( ~ r3_lattice3(sK1,X0,X1)
% 1.18/0.91      | r3_lattices(sK1,X0,k16_lattice3(sK1,X1))
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(k16_lattice3(sK1,X1),u1_struct_0(sK1)) ),
% 1.18/0.91      inference(renaming,[status(thm)],[c_524]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_748,plain,
% 1.18/0.91      ( ~ r3_lattice3(sK1,X0,X1)
% 1.18/0.91      | r3_lattices(sK1,X0,k16_lattice3(sK1,X1))
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.18/0.91      inference(backward_subsumption_resolution,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_737,c_525]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1136,plain,
% 1.18/0.91      ( ~ r3_lattice3(sK1,X0_50,X0_51)
% 1.18/0.91      | r3_lattices(sK1,X0_50,k16_lattice3(sK1,X0_51))
% 1.18/0.91      | ~ m1_subset_1(X0_50,u1_struct_0(sK1)) ),
% 1.18/0.91      inference(subtyping,[status(esa)],[c_748]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1188,plain,
% 1.18/0.91      ( ~ r3_lattice3(sK1,sK2,sK3)
% 1.18/0.91      | r3_lattices(sK1,sK2,k16_lattice3(sK1,sK3))
% 1.18/0.91      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.18/0.91      inference(instantiation,[status(thm)],[c_1136]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1137,plain,
% 1.18/0.91      ( m1_subset_1(k16_lattice3(sK1,X0_51),u1_struct_0(sK1)) ),
% 1.18/0.91      inference(subtyping,[status(esa)],[c_737]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1185,plain,
% 1.18/0.91      ( m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1)) ),
% 1.18/0.91      inference(instantiation,[status(thm)],[c_1137]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_17,negated_conjecture,
% 1.18/0.91      ( k16_lattice3(sK1,sK3) != sK2 ),
% 1.18/0.91      inference(cnf_transformation,[],[f62]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_1149,negated_conjecture,
% 1.18/0.91      ( k16_lattice3(sK1,sK3) != sK2 ),
% 1.18/0.91      inference(subtyping,[status(esa)],[c_17]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_15,plain,
% 1.18/0.91      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 1.18/0.91      | ~ r2_hidden(X2,X1)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ v4_lattice3(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0) ),
% 1.18/0.91      inference(cnf_transformation,[],[f54]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_19,negated_conjecture,
% 1.18/0.91      ( r2_hidden(sK2,sK3) ),
% 1.18/0.91      inference(cnf_transformation,[],[f60]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_364,plain,
% 1.18/0.91      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 1.18/0.91      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.18/0.91      | ~ v4_lattice3(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0)
% 1.18/0.91      | sK2 != X2
% 1.18/0.91      | sK3 != X1 ),
% 1.18/0.91      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_365,plain,
% 1.18/0.91      ( r3_lattices(X0,k16_lattice3(X0,sK3),sK2)
% 1.18/0.91      | ~ m1_subset_1(sK2,u1_struct_0(X0))
% 1.18/0.91      | ~ v4_lattice3(X0)
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0) ),
% 1.18/0.91      inference(unflattening,[status(thm)],[c_364]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_482,plain,
% 1.18/0.91      ( r3_lattices(X0,k16_lattice3(X0,sK3),sK2)
% 1.18/0.91      | ~ m1_subset_1(sK2,u1_struct_0(X0))
% 1.18/0.91      | ~ l3_lattices(X0)
% 1.18/0.91      | v2_struct_0(X0)
% 1.18/0.91      | ~ v10_lattices(X0)
% 1.18/0.91      | sK1 != X0 ),
% 1.18/0.91      inference(resolution_lifted,[status(thm)],[c_365,c_22]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_483,plain,
% 1.18/0.91      ( r3_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
% 1.18/0.91      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.18/0.91      | ~ l3_lattices(sK1)
% 1.18/0.91      | v2_struct_0(sK1)
% 1.18/0.91      | ~ v10_lattices(sK1) ),
% 1.18/0.91      inference(unflattening,[status(thm)],[c_482]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_20,negated_conjecture,
% 1.18/0.91      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.18/0.91      inference(cnf_transformation,[],[f59]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_367,plain,
% 1.18/0.91      ( r3_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
% 1.18/0.91      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.18/0.91      | ~ v4_lattice3(sK1)
% 1.18/0.91      | ~ l3_lattices(sK1)
% 1.18/0.91      | v2_struct_0(sK1)
% 1.18/0.91      | ~ v10_lattices(sK1) ),
% 1.18/0.91      inference(instantiation,[status(thm)],[c_365]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_485,plain,
% 1.18/0.91      ( r3_lattices(sK1,k16_lattice3(sK1,sK3),sK2) ),
% 1.18/0.91      inference(global_propositional_subsumption,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_483,c_24,c_23,c_22,c_21,c_20,c_367]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_807,plain,
% 1.18/0.91      ( r1_lattices(sK1,X0,X1)
% 1.18/0.91      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.18/0.91      | k16_lattice3(sK1,sK3) != X0
% 1.18/0.91      | sK2 != X1
% 1.18/0.91      | sK1 != sK1 ),
% 1.18/0.91      inference(resolution_lifted,[status(thm)],[c_485,c_671]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_808,plain,
% 1.18/0.91      ( r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
% 1.18/0.91      | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
% 1.18/0.91      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.18/0.91      inference(unflattening,[status(thm)],[c_807]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_810,plain,
% 1.18/0.91      ( ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1))
% 1.18/0.91      | r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2) ),
% 1.18/0.91      inference(global_propositional_subsumption,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_808,c_20]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_811,plain,
% 1.18/0.91      ( r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2)
% 1.18/0.91      | ~ m1_subset_1(k16_lattice3(sK1,sK3),u1_struct_0(sK1)) ),
% 1.18/0.91      inference(renaming,[status(thm)],[c_810]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_818,plain,
% 1.18/0.91      ( r1_lattices(sK1,k16_lattice3(sK1,sK3),sK2) ),
% 1.18/0.91      inference(forward_subsumption_resolution,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_811,c_737]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(c_18,negated_conjecture,
% 1.18/0.91      ( r3_lattice3(sK1,sK2,sK3) ),
% 1.18/0.91      inference(cnf_transformation,[],[f61]) ).
% 1.18/0.91  
% 1.18/0.91  cnf(contradiction,plain,
% 1.18/0.91      ( $false ),
% 1.18/0.91      inference(minisat,
% 1.18/0.91                [status(thm)],
% 1.18/0.91                [c_1524,c_1519,c_1188,c_1185,c_1149,c_818,c_18,c_20]) ).
% 1.18/0.91  
% 1.18/0.91  
% 1.18/0.91  % SZS output end CNFRefutation for theBenchmark.p
% 1.18/0.91  
% 1.18/0.91  ------                               Statistics
% 1.18/0.91  
% 1.18/0.91  ------ General
% 1.18/0.91  
% 1.18/0.91  abstr_ref_over_cycles:                  0
% 1.18/0.91  abstr_ref_under_cycles:                 0
% 1.18/0.91  gc_basic_clause_elim:                   0
% 1.18/0.91  forced_gc_time:                         0
% 1.18/0.91  parsing_time:                           0.008
% 1.18/0.91  unif_index_cands_time:                  0.
% 1.18/0.91  unif_index_add_time:                    0.
% 1.18/0.91  orderings_time:                         0.
% 1.18/0.91  out_proof_time:                         0.01
% 1.18/0.91  total_time:                             0.088
% 1.18/0.91  num_of_symbols:                         53
% 1.18/0.91  num_of_terms:                           1038
% 1.18/0.91  
% 1.18/0.91  ------ Preprocessing
% 1.18/0.91  
% 1.18/0.91  num_of_splits:                          0
% 1.18/0.91  num_of_split_atoms:                     0
% 1.18/0.91  num_of_reused_defs:                     0
% 1.18/0.91  num_eq_ax_congr_red:                    33
% 1.18/0.91  num_of_sem_filtered_clauses:            1
% 1.18/0.91  num_of_subtypes:                        4
% 1.18/0.91  monotx_restored_types:                  0
% 1.18/0.91  sat_num_of_epr_types:                   0
% 1.18/0.91  sat_num_of_non_cyclic_types:            0
% 1.18/0.91  sat_guarded_non_collapsed_types:        1
% 1.18/0.91  num_pure_diseq_elim:                    0
% 1.18/0.91  simp_replaced_by:                       0
% 1.18/0.91  res_preprocessed:                       77
% 1.18/0.91  prep_upred:                             0
% 1.18/0.91  prep_unflattend:                        39
% 1.18/0.91  smt_new_axioms:                         0
% 1.18/0.91  pred_elim_cands:                        4
% 1.18/0.91  pred_elim:                              10
% 1.18/0.91  pred_elim_cl:                           10
% 1.18/0.91  pred_elim_cycles:                       12
% 1.18/0.91  merged_defs:                            0
% 1.18/0.91  merged_defs_ncl:                        0
% 1.18/0.91  bin_hyper_res:                          0
% 1.18/0.91  prep_cycles:                            4
% 1.18/0.91  pred_elim_time:                         0.031
% 1.18/0.91  splitting_time:                         0.
% 1.18/0.91  sem_filter_time:                        0.
% 1.18/0.91  monotx_time:                            0.
% 1.18/0.91  subtype_inf_time:                       0.
% 1.18/0.91  
% 1.18/0.91  ------ Problem properties
% 1.18/0.91  
% 1.18/0.91  clauses:                                14
% 1.18/0.91  conjectures:                            3
% 1.18/0.91  epr:                                    1
% 1.18/0.91  horn:                                   12
% 1.18/0.91  ground:                                 5
% 1.18/0.91  unary:                                  7
% 1.18/0.91  binary:                                 0
% 1.18/0.91  lits:                                   35
% 1.18/0.91  lits_eq:                                5
% 1.18/0.91  fd_pure:                                0
% 1.18/0.91  fd_pseudo:                              0
% 1.18/0.91  fd_cond:                                0
% 1.18/0.91  fd_pseudo_cond:                         4
% 1.18/0.91  ac_symbols:                             0
% 1.18/0.91  
% 1.18/0.91  ------ Propositional Solver
% 1.18/0.91  
% 1.18/0.91  prop_solver_calls:                      22
% 1.18/0.91  prop_fast_solver_calls:                 732
% 1.18/0.91  smt_solver_calls:                       0
% 1.18/0.91  smt_fast_solver_calls:                  0
% 1.18/0.91  prop_num_of_clauses:                    295
% 1.18/0.91  prop_preprocess_simplified:             2079
% 1.18/0.91  prop_fo_subsumed:                       47
% 1.18/0.91  prop_solver_time:                       0.
% 1.18/0.91  smt_solver_time:                        0.
% 1.18/0.91  smt_fast_solver_time:                   0.
% 1.18/0.91  prop_fast_solver_time:                  0.
% 1.18/0.91  prop_unsat_core_time:                   0.
% 1.18/0.91  
% 1.18/0.91  ------ QBF
% 1.18/0.91  
% 1.18/0.91  qbf_q_res:                              0
% 1.18/0.91  qbf_num_tautologies:                    0
% 1.18/0.91  qbf_prep_cycles:                        0
% 1.18/0.91  
% 1.18/0.91  ------ BMC1
% 1.18/0.91  
% 1.18/0.91  bmc1_current_bound:                     -1
% 1.18/0.91  bmc1_last_solved_bound:                 -1
% 1.18/0.91  bmc1_unsat_core_size:                   -1
% 1.18/0.91  bmc1_unsat_core_parents_size:           -1
% 1.18/0.91  bmc1_merge_next_fun:                    0
% 1.18/0.91  bmc1_unsat_core_clauses_time:           0.
% 1.18/0.91  
% 1.18/0.91  ------ Instantiation
% 1.18/0.91  
% 1.18/0.91  inst_num_of_clauses:                    22
% 1.18/0.91  inst_num_in_passive:                    5
% 1.18/0.91  inst_num_in_active:                     13
% 1.18/0.91  inst_num_in_unprocessed:                3
% 1.18/0.91  inst_num_of_loops:                      14
% 1.18/0.91  inst_num_of_learning_restarts:          0
% 1.18/0.91  inst_num_moves_active_passive:          0
% 1.18/0.91  inst_lit_activity:                      0
% 1.18/0.91  inst_lit_activity_moves:                0
% 1.18/0.91  inst_num_tautologies:                   0
% 1.18/0.91  inst_num_prop_implied:                  0
% 1.18/0.91  inst_num_existing_simplified:           0
% 1.18/0.91  inst_num_eq_res_simplified:             0
% 1.18/0.91  inst_num_child_elim:                    0
% 1.18/0.91  inst_num_of_dismatching_blockings:      0
% 1.18/0.91  inst_num_of_non_proper_insts:           4
% 1.18/0.91  inst_num_of_duplicates:                 0
% 1.18/0.91  inst_inst_num_from_inst_to_res:         0
% 1.18/0.91  inst_dismatching_checking_time:         0.
% 1.18/0.91  
% 1.18/0.91  ------ Resolution
% 1.18/0.91  
% 1.18/0.91  res_num_of_clauses:                     0
% 1.18/0.91  res_num_in_passive:                     0
% 1.18/0.91  res_num_in_active:                      0
% 1.18/0.91  res_num_of_loops:                       81
% 1.18/0.91  res_forward_subset_subsumed:            0
% 1.18/0.91  res_backward_subset_subsumed:           0
% 1.18/0.91  res_forward_subsumed:                   0
% 1.18/0.91  res_backward_subsumed:                  0
% 1.18/0.91  res_forward_subsumption_resolution:     2
% 1.18/0.91  res_backward_subsumption_resolution:    1
% 1.18/0.91  res_clause_to_clause_subsumption:       60
% 1.18/0.91  res_orphan_elimination:                 0
% 1.18/0.91  res_tautology_del:                      3
% 1.18/0.91  res_num_eq_res_simplified:              0
% 1.18/0.91  res_num_sel_changes:                    0
% 1.18/0.91  res_moves_from_active_to_pass:          0
% 1.18/0.91  
% 1.18/0.91  ------ Superposition
% 1.18/0.91  
% 1.18/0.91  sup_time_total:                         0.
% 1.18/0.91  sup_time_generating:                    0.
% 1.18/0.91  sup_time_sim_full:                      0.
% 1.18/0.91  sup_time_sim_immed:                     0.
% 1.18/0.91  
% 1.18/0.91  sup_num_of_clauses:                     14
% 1.18/0.91  sup_num_in_active:                      2
% 1.18/0.91  sup_num_in_passive:                     12
% 1.18/0.91  sup_num_of_loops:                       2
% 1.18/0.91  sup_fw_superposition:                   0
% 1.18/0.91  sup_bw_superposition:                   0
% 1.18/0.91  sup_immediate_simplified:               0
% 1.18/0.91  sup_given_eliminated:                   0
% 1.18/0.91  comparisons_done:                       0
% 1.18/0.91  comparisons_avoided:                    0
% 1.18/0.91  
% 1.18/0.91  ------ Simplifications
% 1.18/0.91  
% 1.18/0.91  
% 1.18/0.91  sim_fw_subset_subsumed:                 0
% 1.18/0.91  sim_bw_subset_subsumed:                 0
% 1.18/0.91  sim_fw_subsumed:                        0
% 1.18/0.91  sim_bw_subsumed:                        0
% 1.18/0.91  sim_fw_subsumption_res:                 0
% 1.18/0.91  sim_bw_subsumption_res:                 0
% 1.18/0.91  sim_tautology_del:                      0
% 1.18/0.91  sim_eq_tautology_del:                   0
% 1.18/0.91  sim_eq_res_simp:                        0
% 1.18/0.91  sim_fw_demodulated:                     0
% 1.18/0.91  sim_bw_demodulated:                     0
% 1.18/0.91  sim_light_normalised:                   0
% 1.18/0.91  sim_joinable_taut:                      0
% 1.18/0.91  sim_joinable_simp:                      0
% 1.18/0.91  sim_ac_normalised:                      0
% 1.18/0.91  sim_smt_subsumption:                    0
% 1.18/0.91  
%------------------------------------------------------------------------------
