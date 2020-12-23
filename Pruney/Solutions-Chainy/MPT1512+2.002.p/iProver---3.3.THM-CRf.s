%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:16 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  245 (1379 expanded)
%              Number of clauses        :  163 ( 387 expanded)
%              Number of leaves         :   16 ( 324 expanded)
%              Depth                    :   28
%              Number of atoms          : 1191 (8092 expanded)
%              Number of equality atoms :  152 ( 236 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r3_lattices(X0,k16_lattice3(X0,sK5),k16_lattice3(X0,sK4))
          | ~ r3_lattices(X0,k15_lattice3(X0,sK4),k15_lattice3(X0,sK5)) )
        & r1_tarski(sK4,sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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

fof(f54,plain,
    ( ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
      | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) )
    & r1_tarski(sK4,sK5)
    & l3_lattices(sK3)
    & v4_lattice3(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f53,f52])).

fof(f80,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
        & r4_lattice3(X0,sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK2(X0,X1,X2))
                & r4_lattice3(X0,sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f82,plain,(
    v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f14,plain,(
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

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f18])).

fof(f59,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
    | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_718,plain,
    ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_719,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_27,negated_conjecture,
    ( l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_723,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_719,c_27])).

cnf(c_18,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_28,negated_conjecture,
    ( v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_515,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,k15_lattice3(X0,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_516,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | r1_lattices(sK3,k15_lattice3(sK3,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k15_lattice3(sK3,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_29,negated_conjecture,
    ( v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_520,plain,
    ( ~ m1_subset_1(k15_lattice3(sK3,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_lattices(sK3,k15_lattice3(sK3,X1),X0)
    | ~ r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_30,c_29,c_27])).

cnf(c_521,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | r1_lattices(sK3,k15_lattice3(sK3,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(k15_lattice3(sK3,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_520])).

cnf(c_916,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | r1_lattices(sK3,k15_lattice3(sK3,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_723,c_521])).

cnf(c_2078,plain,
    ( ~ r4_lattice3(sK3,X0_52,X0_53)
    | r1_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_916])).

cnf(c_2555,plain,
    ( r4_lattice3(sK3,X0_52,X0_53) != iProver_top
    | r1_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2078])).

cnf(c_2087,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_723])).

cnf(c_2546,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2087])).

cnf(c_1,plain,
    ( ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | v9_lattices(X0) ),
    inference(cnf_transformation,[],[f59])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_389,plain,
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

cnf(c_3,plain,
    ( v6_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2,plain,
    ( v8_lattices(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_393,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_3,c_2])).

cnf(c_645,plain,
    ( ~ r1_lattices(X0,X1,X2)
    | r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_29])).

cnf(c_646,plain,
    ( ~ r1_lattices(sK3,X0,X1)
    | r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_650,plain,
    ( ~ r1_lattices(sK3,X0,X1)
    | r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_30,c_27])).

cnf(c_651,plain,
    ( ~ r1_lattices(sK3,X0,X1)
    | r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_2090,plain,
    ( ~ r1_lattices(sK3,X0_52,X1_52)
    | r3_lattices(sK3,X0_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_651])).

cnf(c_2543,plain,
    ( r1_lattices(sK3,X0_52,X1_52) != iProver_top
    | r3_lattices(sK3,X0_52,X1_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2090])).

cnf(c_3474,plain,
    ( r1_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2543])).

cnf(c_4025,plain,
    ( r4_lattice3(sK3,X0_52,X0_53) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2555,c_3474])).

cnf(c_8,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_871,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_30])).

cnf(c_872,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_871])).

cnf(c_876,plain,
    ( r2_hidden(sK0(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_872,c_27])).

cnf(c_877,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_876])).

cnf(c_2080,plain,
    ( r3_lattice3(sK3,X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0_52,X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_877])).

cnf(c_2553,plain,
    ( r3_lattice3(sK3,X0_52,X0_53) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,X0_52,X0_53),X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2080])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_342,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | sK4 != X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_343,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_2098,plain,
    ( ~ r2_hidden(X0_52,sK4)
    | r2_hidden(X0_52,sK5) ),
    inference(subtyping,[status(esa)],[c_343])).

cnf(c_2535,plain,
    ( r2_hidden(X0_52,sK4) != iProver_top
    | r2_hidden(X0_52,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2098])).

cnf(c_3754,plain,
    ( r3_lattice3(sK3,X0_52,sK4) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,X0_52,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_2535])).

cnf(c_22,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_494,plain,
    ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_495,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_499,plain,
    ( ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r3_lattices(sK3,k16_lattice3(sK3,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_30,c_29,c_27])).

cnf(c_500,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ r2_hidden(X1,X0) ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_2094,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ r2_hidden(X0_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_2539,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_52,X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2094])).

cnf(c_21,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_703,plain,
    ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_704,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_708,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_704,c_27])).

cnf(c_2088,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_708])).

cnf(c_2545,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2088])).

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
    inference(cnf_transformation,[],[f60])).

cnf(c_357,plain,
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

cnf(c_361,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_3,c_2])).

cnf(c_669,plain,
    ( r1_lattices(X0,X1,X2)
    | ~ r3_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_361,c_29])).

cnf(c_670,plain,
    ( r1_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_674,plain,
    ( r1_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_30,c_27])).

cnf(c_675,plain,
    ( r1_lattices(sK3,X0,X1)
    | ~ r3_lattices(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_674])).

cnf(c_2089,plain,
    ( r1_lattices(sK3,X0_52,X1_52)
    | ~ r3_lattices(sK3,X0_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_675])).

cnf(c_2544,plain,
    ( r1_lattices(sK3,X0_52,X1_52) = iProver_top
    | r3_lattices(sK3,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2089])).

cnf(c_3540,plain,
    ( r1_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
    | r3_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2544])).

cnf(c_4077,plain,
    ( r1_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_52,X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2539,c_3540])).

cnf(c_7,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_892,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_30])).

cnf(c_893,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_892])).

cnf(c_897,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_893,c_27])).

cnf(c_898,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_897])).

cnf(c_2079,plain,
    ( r3_lattice3(sK3,X0_52,X0_53)
    | ~ r1_lattices(sK3,X0_52,sK0(sK3,X0_52,X0_53))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_898])).

cnf(c_2554,plain,
    ( r3_lattice3(sK3,X0_52,X0_53) = iProver_top
    | r1_lattices(sK3,X0_52,sK0(sK3,X0_52,X0_53)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2079])).

cnf(c_4322,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53) = iProver_top
    | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_4077,c_2554])).

cnf(c_2146,plain,
    ( m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2088])).

cnf(c_9,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_850,plain,
    ( r3_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_851,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_850])).

cnf(c_855,plain,
    ( m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_851,c_27])).

cnf(c_856,plain,
    ( r3_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_855])).

cnf(c_2081,plain,
    ( r3_lattice3(sK3,X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0_52,X0_53),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_856])).

cnf(c_2744,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53)
    | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3))
    | ~ m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2081])).

cnf(c_2745,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53) = iProver_top
    | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2744])).

cnf(c_5106,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53) = iProver_top
    | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4322,c_2146,c_2745])).

cnf(c_5115,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) = iProver_top
    | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3754,c_5106])).

cnf(c_4033,plain,
    ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2088])).

cnf(c_4034,plain,
    ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4033])).

cnf(c_5356,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5115,c_4034])).

cnf(c_10,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_823,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r1_lattices(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_824,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r1_lattices(sK3,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_823])).

cnf(c_828,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_lattices(sK3,X0,X2)
    | ~ r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_824,c_27])).

cnf(c_829,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r1_lattices(sK3,X0,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X1) ),
    inference(renaming,[status(thm)],[c_828])).

cnf(c_2082,plain,
    ( ~ r3_lattice3(sK3,X0_52,X0_53)
    | r1_lattices(sK3,X0_52,X1_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK3))
    | ~ r2_hidden(X1_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_829])).

cnf(c_2551,plain,
    ( r3_lattice3(sK3,X0_52,X0_53) != iProver_top
    | r1_lattices(sK3,X0_52,X1_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1_52,X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2082])).

cnf(c_3640,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53) != iProver_top
    | r1_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_52,X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2551])).

cnf(c_5361,plain,
    ( r1_lattices(sK3,k16_lattice3(sK3,sK5),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_52,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5356,c_3640])).

cnf(c_3475,plain,
    ( r1_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) != iProver_top
    | r3_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2543])).

cnf(c_5435,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_52,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5361,c_3475])).

cnf(c_25,negated_conjecture,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
    | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2099,negated_conjecture,
    ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
    | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2534,plain,
    ( r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4)) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2099])).

cnf(c_6259,plain,
    ( r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,sK4),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k16_lattice3(sK3,sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5435,c_2534])).

cnf(c_24,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_452,plain,
    ( ~ r3_lattice3(X0,X1,X2)
    | r3_lattices(X0,X1,k16_lattice3(X0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_453,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ r3_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_30,c_29,c_27])).

cnf(c_458,plain,
    ( ~ r3_lattice3(sK3,X0,X1)
    | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_457])).

cnf(c_2096,plain,
    ( ~ r3_lattice3(sK3,X0_52,X0_53)
    | r3_lattices(sK3,X0_52,k16_lattice3(sK3,X0_53))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_2537,plain,
    ( r3_lattice3(sK3,X0_52,X0_53) != iProver_top
    | r3_lattices(sK3,X0_52,k16_lattice3(sK3,X0_53)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2096])).

cnf(c_3052,plain,
    ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) != iProver_top
    | r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top
    | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_2534])).

cnf(c_6316,plain,
    ( r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6259,c_3052,c_4034,c_5115])).

cnf(c_6326,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,sK5),sK4) != iProver_top
    | m1_subset_1(k15_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4025,c_6316])).

cnf(c_12,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_781,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_782,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,X1),X1)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_786,plain,
    ( r2_hidden(sK1(sK3,X0,X1),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_27])).

cnf(c_787,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,X1),X1) ),
    inference(renaming,[status(thm)],[c_786])).

cnf(c_2084,plain,
    ( r4_lattice3(sK3,X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0_52,X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_787])).

cnf(c_2549,plain,
    ( r4_lattice3(sK3,X0_52,X0_53) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0_52,X0_53),X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2084])).

cnf(c_3707,plain,
    ( r4_lattice3(sK3,X0_52,sK4) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0_52,sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2549,c_2535])).

cnf(c_19,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_182,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ v4_lattice3(X0)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_20])).

cnf(c_437,plain,
    ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0)
    | ~ v10_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_182,c_28])).

cnf(c_438,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,X0),X0)
    | ~ l3_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ v10_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,X0),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_30,c_29,c_27])).

cnf(c_2097,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_2536,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2097])).

cnf(c_14,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_733,plain,
    ( ~ r4_lattice3(X0,X1,X2)
    | r1_lattices(X0,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_734,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | r1_lattices(sK3,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X1)
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_738,plain,
    ( ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_lattices(sK3,X2,X0)
    | ~ r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_734,c_27])).

cnf(c_739,plain,
    ( ~ r4_lattice3(sK3,X0,X1)
    | r1_lattices(sK3,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ r2_hidden(X2,X1) ),
    inference(renaming,[status(thm)],[c_738])).

cnf(c_2086,plain,
    ( ~ r4_lattice3(sK3,X0_52,X0_53)
    | r1_lattices(sK3,X1_52,X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_52,u1_struct_0(sK3))
    | ~ r2_hidden(X1_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_739])).

cnf(c_2547,plain,
    ( r4_lattice3(sK3,X0_52,X0_53) != iProver_top
    | r1_lattices(sK3,X1_52,X0_52) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1_52,X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2086])).

cnf(c_3591,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53) != iProver_top
    | r1_lattices(sK3,X0_52,k15_lattice3(sK3,X0_53)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_52,X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2547])).

cnf(c_4354,plain,
    ( r1_lattices(sK3,X0_52,k15_lattice3(sK3,X0_53)) = iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0_52,X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2536,c_3591])).

cnf(c_11,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_802,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_30])).

cnf(c_803,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_807,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_27])).

cnf(c_808,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_807])).

cnf(c_2083,plain,
    ( r4_lattice3(sK3,X0_52,X0_53)
    | ~ r1_lattices(sK3,sK1(sK3,X0_52,X0_53),X0_52)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_808])).

cnf(c_2550,plain,
    ( r4_lattice3(sK3,X0_52,X0_53) = iProver_top
    | r1_lattices(sK3,sK1(sK3,X0_52,X0_53),X0_52) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2083])).

cnf(c_4409,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53) = iProver_top
    | m1_subset_1(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_4354,c_2550])).

cnf(c_2149,plain,
    ( m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2087])).

cnf(c_13,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_760,plain,
    ( r4_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_761,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
    | ~ l3_lattices(sK3) ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_765,plain,
    ( m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r4_lattice3(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_761,c_27])).

cnf(c_766,plain,
    ( r4_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(renaming,[status(thm)],[c_765])).

cnf(c_2085,plain,
    ( r4_lattice3(sK3,X0_52,X0_53)
    | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0_52,X0_53),u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_766])).

cnf(c_2749,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53)
    | m1_subset_1(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3))
    | ~ m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_2750,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53) = iProver_top
    | m1_subset_1(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2749])).

cnf(c_5206,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53) = iProver_top
    | r2_hidden(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4409,c_2149,c_2750])).

cnf(c_5213,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,sK5),sK4) = iProver_top
    | m1_subset_1(k15_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3707,c_5206])).

cnf(c_5378,plain,
    ( r4_lattice3(sK3,k15_lattice3(sK3,sK5),sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5213,c_2546])).

cnf(c_6349,plain,
    ( m1_subset_1(k15_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6326,c_5378])).

cnf(c_6354,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6349,c_2546])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:40:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.33  % Running in FOF mode
% 2.08/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/0.99  
% 2.08/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/0.99  
% 2.08/0.99  ------  iProver source info
% 2.08/0.99  
% 2.08/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.08/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/0.99  git: non_committed_changes: false
% 2.08/0.99  git: last_make_outside_of_git: false
% 2.08/0.99  
% 2.08/0.99  ------ 
% 2.08/0.99  
% 2.08/0.99  ------ Input Options
% 2.08/0.99  
% 2.08/0.99  --out_options                           all
% 2.08/0.99  --tptp_safe_out                         true
% 2.08/0.99  --problem_path                          ""
% 2.08/0.99  --include_path                          ""
% 2.08/0.99  --clausifier                            res/vclausify_rel
% 2.08/0.99  --clausifier_options                    --mode clausify
% 2.08/0.99  --stdin                                 false
% 2.08/0.99  --stats_out                             all
% 2.08/0.99  
% 2.08/0.99  ------ General Options
% 2.08/0.99  
% 2.08/0.99  --fof                                   false
% 2.08/0.99  --time_out_real                         305.
% 2.08/0.99  --time_out_virtual                      -1.
% 2.08/0.99  --symbol_type_check                     false
% 2.08/0.99  --clausify_out                          false
% 2.08/0.99  --sig_cnt_out                           false
% 2.08/0.99  --trig_cnt_out                          false
% 2.08/0.99  --trig_cnt_out_tolerance                1.
% 2.08/0.99  --trig_cnt_out_sk_spl                   false
% 2.08/0.99  --abstr_cl_out                          false
% 2.08/0.99  
% 2.08/0.99  ------ Global Options
% 2.08/0.99  
% 2.08/0.99  --schedule                              default
% 2.08/0.99  --add_important_lit                     false
% 2.08/0.99  --prop_solver_per_cl                    1000
% 2.08/0.99  --min_unsat_core                        false
% 2.08/0.99  --soft_assumptions                      false
% 2.08/0.99  --soft_lemma_size                       3
% 2.08/0.99  --prop_impl_unit_size                   0
% 2.08/0.99  --prop_impl_unit                        []
% 2.08/0.99  --share_sel_clauses                     true
% 2.08/0.99  --reset_solvers                         false
% 2.08/0.99  --bc_imp_inh                            [conj_cone]
% 2.08/0.99  --conj_cone_tolerance                   3.
% 2.08/0.99  --extra_neg_conj                        none
% 2.08/0.99  --large_theory_mode                     true
% 2.08/0.99  --prolific_symb_bound                   200
% 2.08/0.99  --lt_threshold                          2000
% 2.08/0.99  --clause_weak_htbl                      true
% 2.08/0.99  --gc_record_bc_elim                     false
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing Options
% 2.08/0.99  
% 2.08/0.99  --preprocessing_flag                    true
% 2.08/0.99  --time_out_prep_mult                    0.1
% 2.08/0.99  --splitting_mode                        input
% 2.08/0.99  --splitting_grd                         true
% 2.08/0.99  --splitting_cvd                         false
% 2.08/0.99  --splitting_cvd_svl                     false
% 2.08/0.99  --splitting_nvd                         32
% 2.08/0.99  --sub_typing                            true
% 2.08/0.99  --prep_gs_sim                           true
% 2.08/0.99  --prep_unflatten                        true
% 2.08/0.99  --prep_res_sim                          true
% 2.08/0.99  --prep_upred                            true
% 2.08/0.99  --prep_sem_filter                       exhaustive
% 2.08/0.99  --prep_sem_filter_out                   false
% 2.08/0.99  --pred_elim                             true
% 2.08/0.99  --res_sim_input                         true
% 2.08/0.99  --eq_ax_congr_red                       true
% 2.08/0.99  --pure_diseq_elim                       true
% 2.08/0.99  --brand_transform                       false
% 2.08/0.99  --non_eq_to_eq                          false
% 2.08/0.99  --prep_def_merge                        true
% 2.08/0.99  --prep_def_merge_prop_impl              false
% 2.08/0.99  --prep_def_merge_mbd                    true
% 2.08/0.99  --prep_def_merge_tr_red                 false
% 2.08/0.99  --prep_def_merge_tr_cl                  false
% 2.08/0.99  --smt_preprocessing                     true
% 2.08/0.99  --smt_ac_axioms                         fast
% 2.08/0.99  --preprocessed_out                      false
% 2.08/0.99  --preprocessed_stats                    false
% 2.08/0.99  
% 2.08/0.99  ------ Abstraction refinement Options
% 2.08/0.99  
% 2.08/0.99  --abstr_ref                             []
% 2.08/0.99  --abstr_ref_prep                        false
% 2.08/0.99  --abstr_ref_until_sat                   false
% 2.08/0.99  --abstr_ref_sig_restrict                funpre
% 2.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.99  --abstr_ref_under                       []
% 2.08/0.99  
% 2.08/0.99  ------ SAT Options
% 2.08/0.99  
% 2.08/0.99  --sat_mode                              false
% 2.08/0.99  --sat_fm_restart_options                ""
% 2.08/0.99  --sat_gr_def                            false
% 2.08/0.99  --sat_epr_types                         true
% 2.08/0.99  --sat_non_cyclic_types                  false
% 2.08/0.99  --sat_finite_models                     false
% 2.08/0.99  --sat_fm_lemmas                         false
% 2.08/0.99  --sat_fm_prep                           false
% 2.08/0.99  --sat_fm_uc_incr                        true
% 2.08/0.99  --sat_out_model                         small
% 2.08/0.99  --sat_out_clauses                       false
% 2.08/0.99  
% 2.08/0.99  ------ QBF Options
% 2.08/0.99  
% 2.08/0.99  --qbf_mode                              false
% 2.08/0.99  --qbf_elim_univ                         false
% 2.08/0.99  --qbf_dom_inst                          none
% 2.08/0.99  --qbf_dom_pre_inst                      false
% 2.08/0.99  --qbf_sk_in                             false
% 2.08/0.99  --qbf_pred_elim                         true
% 2.08/0.99  --qbf_split                             512
% 2.08/0.99  
% 2.08/0.99  ------ BMC1 Options
% 2.08/0.99  
% 2.08/0.99  --bmc1_incremental                      false
% 2.08/0.99  --bmc1_axioms                           reachable_all
% 2.08/0.99  --bmc1_min_bound                        0
% 2.08/0.99  --bmc1_max_bound                        -1
% 2.08/0.99  --bmc1_max_bound_default                -1
% 2.08/0.99  --bmc1_symbol_reachability              true
% 2.08/0.99  --bmc1_property_lemmas                  false
% 2.08/0.99  --bmc1_k_induction                      false
% 2.08/0.99  --bmc1_non_equiv_states                 false
% 2.08/0.99  --bmc1_deadlock                         false
% 2.08/0.99  --bmc1_ucm                              false
% 2.08/0.99  --bmc1_add_unsat_core                   none
% 2.08/0.99  --bmc1_unsat_core_children              false
% 2.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.99  --bmc1_out_stat                         full
% 2.08/0.99  --bmc1_ground_init                      false
% 2.08/0.99  --bmc1_pre_inst_next_state              false
% 2.08/0.99  --bmc1_pre_inst_state                   false
% 2.08/0.99  --bmc1_pre_inst_reach_state             false
% 2.08/0.99  --bmc1_out_unsat_core                   false
% 2.08/0.99  --bmc1_aig_witness_out                  false
% 2.08/0.99  --bmc1_verbose                          false
% 2.08/0.99  --bmc1_dump_clauses_tptp                false
% 2.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.99  --bmc1_dump_file                        -
% 2.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.99  --bmc1_ucm_extend_mode                  1
% 2.08/0.99  --bmc1_ucm_init_mode                    2
% 2.08/0.99  --bmc1_ucm_cone_mode                    none
% 2.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.99  --bmc1_ucm_relax_model                  4
% 2.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.99  --bmc1_ucm_layered_model                none
% 2.08/0.99  --bmc1_ucm_max_lemma_size               10
% 2.08/0.99  
% 2.08/0.99  ------ AIG Options
% 2.08/0.99  
% 2.08/0.99  --aig_mode                              false
% 2.08/0.99  
% 2.08/0.99  ------ Instantiation Options
% 2.08/0.99  
% 2.08/0.99  --instantiation_flag                    true
% 2.08/0.99  --inst_sos_flag                         false
% 2.08/0.99  --inst_sos_phase                        true
% 2.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel_side                     num_symb
% 2.08/0.99  --inst_solver_per_active                1400
% 2.08/0.99  --inst_solver_calls_frac                1.
% 2.08/0.99  --inst_passive_queue_type               priority_queues
% 2.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.99  --inst_passive_queues_freq              [25;2]
% 2.08/0.99  --inst_dismatching                      true
% 2.08/0.99  --inst_eager_unprocessed_to_passive     true
% 2.08/0.99  --inst_prop_sim_given                   true
% 2.08/0.99  --inst_prop_sim_new                     false
% 2.08/0.99  --inst_subs_new                         false
% 2.08/0.99  --inst_eq_res_simp                      false
% 2.08/0.99  --inst_subs_given                       false
% 2.08/0.99  --inst_orphan_elimination               true
% 2.08/0.99  --inst_learning_loop_flag               true
% 2.08/0.99  --inst_learning_start                   3000
% 2.08/0.99  --inst_learning_factor                  2
% 2.08/0.99  --inst_start_prop_sim_after_learn       3
% 2.08/0.99  --inst_sel_renew                        solver
% 2.08/0.99  --inst_lit_activity_flag                true
% 2.08/0.99  --inst_restr_to_given                   false
% 2.08/0.99  --inst_activity_threshold               500
% 2.08/0.99  --inst_out_proof                        true
% 2.08/0.99  
% 2.08/0.99  ------ Resolution Options
% 2.08/0.99  
% 2.08/0.99  --resolution_flag                       true
% 2.08/0.99  --res_lit_sel                           adaptive
% 2.08/0.99  --res_lit_sel_side                      none
% 2.08/0.99  --res_ordering                          kbo
% 2.08/0.99  --res_to_prop_solver                    active
% 2.08/0.99  --res_prop_simpl_new                    false
% 2.08/0.99  --res_prop_simpl_given                  true
% 2.08/0.99  --res_passive_queue_type                priority_queues
% 2.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.99  --res_passive_queues_freq               [15;5]
% 2.08/0.99  --res_forward_subs                      full
% 2.08/0.99  --res_backward_subs                     full
% 2.08/0.99  --res_forward_subs_resolution           true
% 2.08/0.99  --res_backward_subs_resolution          true
% 2.08/0.99  --res_orphan_elimination                true
% 2.08/0.99  --res_time_limit                        2.
% 2.08/0.99  --res_out_proof                         true
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Options
% 2.08/0.99  
% 2.08/0.99  --superposition_flag                    true
% 2.08/0.99  --sup_passive_queue_type                priority_queues
% 2.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.99  --demod_completeness_check              fast
% 2.08/0.99  --demod_use_ground                      true
% 2.08/0.99  --sup_to_prop_solver                    passive
% 2.08/0.99  --sup_prop_simpl_new                    true
% 2.08/0.99  --sup_prop_simpl_given                  true
% 2.08/0.99  --sup_fun_splitting                     false
% 2.08/0.99  --sup_smt_interval                      50000
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Simplification Setup
% 2.08/0.99  
% 2.08/0.99  --sup_indices_passive                   []
% 2.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_full_bw                           [BwDemod]
% 2.08/0.99  --sup_immed_triv                        [TrivRules]
% 2.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_immed_bw_main                     []
% 2.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  
% 2.08/0.99  ------ Combination Options
% 2.08/0.99  
% 2.08/0.99  --comb_res_mult                         3
% 2.08/0.99  --comb_sup_mult                         2
% 2.08/0.99  --comb_inst_mult                        10
% 2.08/0.99  
% 2.08/0.99  ------ Debug Options
% 2.08/0.99  
% 2.08/0.99  --dbg_backtrace                         false
% 2.08/0.99  --dbg_dump_prop_clauses                 false
% 2.08/0.99  --dbg_dump_prop_clauses_file            -
% 2.08/0.99  --dbg_out_stat                          false
% 2.08/0.99  ------ Parsing...
% 2.08/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/0.99  ------ Proving...
% 2.08/0.99  ------ Problem Properties 
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  clauses                                 22
% 2.08/0.99  conjectures                             1
% 2.08/0.99  EPR                                     1
% 2.08/0.99  Horn                                    16
% 2.08/0.99  unary                                   3
% 2.08/0.99  binary                                  2
% 2.08/0.99  lits                                    67
% 2.08/0.99  lits eq                                 3
% 2.08/0.99  fd_pure                                 0
% 2.08/0.99  fd_pseudo                               0
% 2.08/0.99  fd_cond                                 0
% 2.08/0.99  fd_pseudo_cond                          3
% 2.08/0.99  AC symbols                              0
% 2.08/0.99  
% 2.08/0.99  ------ Schedule dynamic 5 is on 
% 2.08/0.99  
% 2.08/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  ------ 
% 2.08/0.99  Current options:
% 2.08/0.99  ------ 
% 2.08/0.99  
% 2.08/0.99  ------ Input Options
% 2.08/0.99  
% 2.08/0.99  --out_options                           all
% 2.08/0.99  --tptp_safe_out                         true
% 2.08/0.99  --problem_path                          ""
% 2.08/0.99  --include_path                          ""
% 2.08/0.99  --clausifier                            res/vclausify_rel
% 2.08/0.99  --clausifier_options                    --mode clausify
% 2.08/0.99  --stdin                                 false
% 2.08/0.99  --stats_out                             all
% 2.08/0.99  
% 2.08/0.99  ------ General Options
% 2.08/0.99  
% 2.08/0.99  --fof                                   false
% 2.08/0.99  --time_out_real                         305.
% 2.08/0.99  --time_out_virtual                      -1.
% 2.08/0.99  --symbol_type_check                     false
% 2.08/0.99  --clausify_out                          false
% 2.08/0.99  --sig_cnt_out                           false
% 2.08/0.99  --trig_cnt_out                          false
% 2.08/0.99  --trig_cnt_out_tolerance                1.
% 2.08/0.99  --trig_cnt_out_sk_spl                   false
% 2.08/0.99  --abstr_cl_out                          false
% 2.08/0.99  
% 2.08/0.99  ------ Global Options
% 2.08/0.99  
% 2.08/0.99  --schedule                              default
% 2.08/0.99  --add_important_lit                     false
% 2.08/0.99  --prop_solver_per_cl                    1000
% 2.08/0.99  --min_unsat_core                        false
% 2.08/0.99  --soft_assumptions                      false
% 2.08/0.99  --soft_lemma_size                       3
% 2.08/0.99  --prop_impl_unit_size                   0
% 2.08/0.99  --prop_impl_unit                        []
% 2.08/0.99  --share_sel_clauses                     true
% 2.08/0.99  --reset_solvers                         false
% 2.08/0.99  --bc_imp_inh                            [conj_cone]
% 2.08/0.99  --conj_cone_tolerance                   3.
% 2.08/0.99  --extra_neg_conj                        none
% 2.08/0.99  --large_theory_mode                     true
% 2.08/0.99  --prolific_symb_bound                   200
% 2.08/0.99  --lt_threshold                          2000
% 2.08/0.99  --clause_weak_htbl                      true
% 2.08/0.99  --gc_record_bc_elim                     false
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing Options
% 2.08/0.99  
% 2.08/0.99  --preprocessing_flag                    true
% 2.08/0.99  --time_out_prep_mult                    0.1
% 2.08/0.99  --splitting_mode                        input
% 2.08/0.99  --splitting_grd                         true
% 2.08/0.99  --splitting_cvd                         false
% 2.08/0.99  --splitting_cvd_svl                     false
% 2.08/0.99  --splitting_nvd                         32
% 2.08/0.99  --sub_typing                            true
% 2.08/0.99  --prep_gs_sim                           true
% 2.08/0.99  --prep_unflatten                        true
% 2.08/0.99  --prep_res_sim                          true
% 2.08/0.99  --prep_upred                            true
% 2.08/0.99  --prep_sem_filter                       exhaustive
% 2.08/0.99  --prep_sem_filter_out                   false
% 2.08/0.99  --pred_elim                             true
% 2.08/0.99  --res_sim_input                         true
% 2.08/0.99  --eq_ax_congr_red                       true
% 2.08/0.99  --pure_diseq_elim                       true
% 2.08/0.99  --brand_transform                       false
% 2.08/0.99  --non_eq_to_eq                          false
% 2.08/0.99  --prep_def_merge                        true
% 2.08/0.99  --prep_def_merge_prop_impl              false
% 2.08/0.99  --prep_def_merge_mbd                    true
% 2.08/0.99  --prep_def_merge_tr_red                 false
% 2.08/0.99  --prep_def_merge_tr_cl                  false
% 2.08/0.99  --smt_preprocessing                     true
% 2.08/0.99  --smt_ac_axioms                         fast
% 2.08/0.99  --preprocessed_out                      false
% 2.08/0.99  --preprocessed_stats                    false
% 2.08/0.99  
% 2.08/0.99  ------ Abstraction refinement Options
% 2.08/0.99  
% 2.08/0.99  --abstr_ref                             []
% 2.08/0.99  --abstr_ref_prep                        false
% 2.08/0.99  --abstr_ref_until_sat                   false
% 2.08/0.99  --abstr_ref_sig_restrict                funpre
% 2.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.99  --abstr_ref_under                       []
% 2.08/0.99  
% 2.08/0.99  ------ SAT Options
% 2.08/0.99  
% 2.08/0.99  --sat_mode                              false
% 2.08/0.99  --sat_fm_restart_options                ""
% 2.08/0.99  --sat_gr_def                            false
% 2.08/0.99  --sat_epr_types                         true
% 2.08/0.99  --sat_non_cyclic_types                  false
% 2.08/0.99  --sat_finite_models                     false
% 2.08/0.99  --sat_fm_lemmas                         false
% 2.08/0.99  --sat_fm_prep                           false
% 2.08/0.99  --sat_fm_uc_incr                        true
% 2.08/0.99  --sat_out_model                         small
% 2.08/0.99  --sat_out_clauses                       false
% 2.08/0.99  
% 2.08/0.99  ------ QBF Options
% 2.08/0.99  
% 2.08/0.99  --qbf_mode                              false
% 2.08/0.99  --qbf_elim_univ                         false
% 2.08/0.99  --qbf_dom_inst                          none
% 2.08/0.99  --qbf_dom_pre_inst                      false
% 2.08/0.99  --qbf_sk_in                             false
% 2.08/0.99  --qbf_pred_elim                         true
% 2.08/0.99  --qbf_split                             512
% 2.08/0.99  
% 2.08/0.99  ------ BMC1 Options
% 2.08/0.99  
% 2.08/0.99  --bmc1_incremental                      false
% 2.08/0.99  --bmc1_axioms                           reachable_all
% 2.08/0.99  --bmc1_min_bound                        0
% 2.08/0.99  --bmc1_max_bound                        -1
% 2.08/0.99  --bmc1_max_bound_default                -1
% 2.08/0.99  --bmc1_symbol_reachability              true
% 2.08/0.99  --bmc1_property_lemmas                  false
% 2.08/0.99  --bmc1_k_induction                      false
% 2.08/0.99  --bmc1_non_equiv_states                 false
% 2.08/0.99  --bmc1_deadlock                         false
% 2.08/0.99  --bmc1_ucm                              false
% 2.08/0.99  --bmc1_add_unsat_core                   none
% 2.08/0.99  --bmc1_unsat_core_children              false
% 2.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.99  --bmc1_out_stat                         full
% 2.08/0.99  --bmc1_ground_init                      false
% 2.08/0.99  --bmc1_pre_inst_next_state              false
% 2.08/0.99  --bmc1_pre_inst_state                   false
% 2.08/0.99  --bmc1_pre_inst_reach_state             false
% 2.08/0.99  --bmc1_out_unsat_core                   false
% 2.08/0.99  --bmc1_aig_witness_out                  false
% 2.08/0.99  --bmc1_verbose                          false
% 2.08/0.99  --bmc1_dump_clauses_tptp                false
% 2.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.99  --bmc1_dump_file                        -
% 2.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.99  --bmc1_ucm_extend_mode                  1
% 2.08/0.99  --bmc1_ucm_init_mode                    2
% 2.08/0.99  --bmc1_ucm_cone_mode                    none
% 2.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.99  --bmc1_ucm_relax_model                  4
% 2.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.99  --bmc1_ucm_layered_model                none
% 2.08/0.99  --bmc1_ucm_max_lemma_size               10
% 2.08/0.99  
% 2.08/0.99  ------ AIG Options
% 2.08/0.99  
% 2.08/0.99  --aig_mode                              false
% 2.08/0.99  
% 2.08/0.99  ------ Instantiation Options
% 2.08/0.99  
% 2.08/0.99  --instantiation_flag                    true
% 2.08/0.99  --inst_sos_flag                         false
% 2.08/0.99  --inst_sos_phase                        true
% 2.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel_side                     none
% 2.08/0.99  --inst_solver_per_active                1400
% 2.08/0.99  --inst_solver_calls_frac                1.
% 2.08/0.99  --inst_passive_queue_type               priority_queues
% 2.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.99  --inst_passive_queues_freq              [25;2]
% 2.08/0.99  --inst_dismatching                      true
% 2.08/0.99  --inst_eager_unprocessed_to_passive     true
% 2.08/0.99  --inst_prop_sim_given                   true
% 2.08/0.99  --inst_prop_sim_new                     false
% 2.08/0.99  --inst_subs_new                         false
% 2.08/0.99  --inst_eq_res_simp                      false
% 2.08/0.99  --inst_subs_given                       false
% 2.08/0.99  --inst_orphan_elimination               true
% 2.08/0.99  --inst_learning_loop_flag               true
% 2.08/0.99  --inst_learning_start                   3000
% 2.08/0.99  --inst_learning_factor                  2
% 2.08/0.99  --inst_start_prop_sim_after_learn       3
% 2.08/0.99  --inst_sel_renew                        solver
% 2.08/0.99  --inst_lit_activity_flag                true
% 2.08/0.99  --inst_restr_to_given                   false
% 2.08/0.99  --inst_activity_threshold               500
% 2.08/0.99  --inst_out_proof                        true
% 2.08/0.99  
% 2.08/0.99  ------ Resolution Options
% 2.08/0.99  
% 2.08/0.99  --resolution_flag                       false
% 2.08/0.99  --res_lit_sel                           adaptive
% 2.08/0.99  --res_lit_sel_side                      none
% 2.08/0.99  --res_ordering                          kbo
% 2.08/0.99  --res_to_prop_solver                    active
% 2.08/0.99  --res_prop_simpl_new                    false
% 2.08/0.99  --res_prop_simpl_given                  true
% 2.08/0.99  --res_passive_queue_type                priority_queues
% 2.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.99  --res_passive_queues_freq               [15;5]
% 2.08/0.99  --res_forward_subs                      full
% 2.08/0.99  --res_backward_subs                     full
% 2.08/0.99  --res_forward_subs_resolution           true
% 2.08/0.99  --res_backward_subs_resolution          true
% 2.08/0.99  --res_orphan_elimination                true
% 2.08/0.99  --res_time_limit                        2.
% 2.08/0.99  --res_out_proof                         true
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Options
% 2.08/0.99  
% 2.08/0.99  --superposition_flag                    true
% 2.08/0.99  --sup_passive_queue_type                priority_queues
% 2.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.99  --demod_completeness_check              fast
% 2.08/0.99  --demod_use_ground                      true
% 2.08/0.99  --sup_to_prop_solver                    passive
% 2.08/0.99  --sup_prop_simpl_new                    true
% 2.08/0.99  --sup_prop_simpl_given                  true
% 2.08/0.99  --sup_fun_splitting                     false
% 2.08/0.99  --sup_smt_interval                      50000
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Simplification Setup
% 2.08/0.99  
% 2.08/0.99  --sup_indices_passive                   []
% 2.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_full_bw                           [BwDemod]
% 2.08/0.99  --sup_immed_triv                        [TrivRules]
% 2.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_immed_bw_main                     []
% 2.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  
% 2.08/0.99  ------ Combination Options
% 2.08/0.99  
% 2.08/0.99  --comb_res_mult                         3
% 2.08/0.99  --comb_sup_mult                         2
% 2.08/0.99  --comb_inst_mult                        10
% 2.08/0.99  
% 2.08/0.99  ------ Debug Options
% 2.08/0.99  
% 2.08/0.99  --dbg_backtrace                         false
% 2.08/0.99  --dbg_dump_prop_clauses                 false
% 2.08/0.99  --dbg_dump_prop_clauses_file            -
% 2.08/0.99  --dbg_out_stat                          false
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  ------ Proving...
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  % SZS status Theorem for theBenchmark.p
% 2.08/0.99  
% 2.08/0.99   Resolution empty clause
% 2.08/0.99  
% 2.08/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/0.99  
% 2.08/0.99  fof(f7,axiom,(
% 2.08/0.99    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f28,plain,(
% 2.08/0.99    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f7])).
% 2.08/0.99  
% 2.08/0.99  fof(f29,plain,(
% 2.08/0.99    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f28])).
% 2.08/0.99  
% 2.08/0.99  fof(f75,plain,(
% 2.08/0.99    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f29])).
% 2.08/0.99  
% 2.08/0.99  fof(f11,conjecture,(
% 2.08/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f12,negated_conjecture,(
% 2.08/0.99    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 2.08/0.99    inference(negated_conjecture,[],[f11])).
% 2.08/0.99  
% 2.08/0.99  fof(f36,plain,(
% 2.08/0.99    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f12])).
% 2.08/0.99  
% 2.08/0.99  fof(f37,plain,(
% 2.08/0.99    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f36])).
% 2.08/0.99  
% 2.08/0.99  fof(f53,plain,(
% 2.08/0.99    ( ! [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) => ((~r3_lattices(X0,k16_lattice3(X0,sK5),k16_lattice3(X0,sK4)) | ~r3_lattices(X0,k15_lattice3(X0,sK4),k15_lattice3(X0,sK5))) & r1_tarski(sK4,sK5))) )),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f52,plain,(
% 2.08/0.99    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : ((~r3_lattices(sK3,k16_lattice3(sK3,X2),k16_lattice3(sK3,X1)) | ~r3_lattices(sK3,k15_lattice3(sK3,X1),k15_lattice3(sK3,X2))) & r1_tarski(X1,X2)) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f54,plain,(
% 2.08/0.99    ((~r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4)) | ~r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5))) & r1_tarski(sK4,sK5)) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f53,f52])).
% 2.08/0.99  
% 2.08/0.99  fof(f80,plain,(
% 2.08/0.99    ~v2_struct_0(sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f54])).
% 2.08/0.99  
% 2.08/0.99  fof(f83,plain,(
% 2.08/0.99    l3_lattices(sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f54])).
% 2.08/0.99  
% 2.08/0.99  fof(f6,axiom,(
% 2.08/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f26,plain,(
% 2.08/0.99    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f6])).
% 2.08/0.99  
% 2.08/0.99  fof(f27,plain,(
% 2.08/0.99    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f26])).
% 2.08/0.99  
% 2.08/0.99  fof(f47,plain,(
% 2.08/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(nnf_transformation,[],[f27])).
% 2.08/0.99  
% 2.08/0.99  fof(f48,plain,(
% 2.08/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f47])).
% 2.08/0.99  
% 2.08/0.99  fof(f49,plain,(
% 2.08/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(rectify,[],[f48])).
% 2.08/0.99  
% 2.08/0.99  fof(f50,plain,(
% 2.08/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f51,plain,(
% 2.08/0.99    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK2(X0,X1,X2)) & r4_lattice3(X0,sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 2.08/0.99  
% 2.08/0.99  fof(f71,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f51])).
% 2.08/0.99  
% 2.08/0.99  fof(f86,plain,(
% 2.08/0.99    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(equality_resolution,[],[f71])).
% 2.08/0.99  
% 2.08/0.99  fof(f82,plain,(
% 2.08/0.99    v4_lattice3(sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f54])).
% 2.08/0.99  
% 2.08/0.99  fof(f81,plain,(
% 2.08/0.99    v10_lattices(sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f54])).
% 2.08/0.99  
% 2.08/0.99  fof(f2,axiom,(
% 2.08/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f14,plain,(
% 2.08/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.08/0.99    inference(pure_predicate_removal,[],[f2])).
% 2.08/0.99  
% 2.08/0.99  fof(f15,plain,(
% 2.08/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.08/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.08/0.99  
% 2.08/0.99  fof(f16,plain,(
% 2.08/0.99    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 2.08/0.99    inference(pure_predicate_removal,[],[f15])).
% 2.08/0.99  
% 2.08/0.99  fof(f18,plain,(
% 2.08/0.99    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.08/0.99    inference(ennf_transformation,[],[f16])).
% 2.08/0.99  
% 2.08/0.99  fof(f19,plain,(
% 2.08/0.99    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.08/0.99    inference(flattening,[],[f18])).
% 2.08/0.99  
% 2.08/0.99  fof(f59,plain,(
% 2.08/0.99    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f19])).
% 2.08/0.99  
% 2.08/0.99  fof(f3,axiom,(
% 2.08/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f20,plain,(
% 2.08/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f3])).
% 2.08/0.99  
% 2.08/0.99  fof(f21,plain,(
% 2.08/0.99    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f20])).
% 2.08/0.99  
% 2.08/0.99  fof(f38,plain,(
% 2.08/0.99    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(nnf_transformation,[],[f21])).
% 2.08/0.99  
% 2.08/0.99  fof(f61,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f38])).
% 2.08/0.99  
% 2.08/0.99  fof(f57,plain,(
% 2.08/0.99    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f19])).
% 2.08/0.99  
% 2.08/0.99  fof(f58,plain,(
% 2.08/0.99    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f19])).
% 2.08/0.99  
% 2.08/0.99  fof(f4,axiom,(
% 2.08/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f22,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f4])).
% 2.08/0.99  
% 2.08/0.99  fof(f23,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f22])).
% 2.08/0.99  
% 2.08/0.99  fof(f39,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(nnf_transformation,[],[f23])).
% 2.08/0.99  
% 2.08/0.99  fof(f40,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(rectify,[],[f39])).
% 2.08/0.99  
% 2.08/0.99  fof(f41,plain,(
% 2.08/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f42,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 2.08/0.99  
% 2.08/0.99  fof(f64,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f42])).
% 2.08/0.99  
% 2.08/0.99  fof(f1,axiom,(
% 2.08/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f13,plain,(
% 2.08/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.08/0.99  
% 2.08/0.99  fof(f17,plain,(
% 2.08/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.08/0.99    inference(ennf_transformation,[],[f13])).
% 2.08/0.99  
% 2.08/0.99  fof(f55,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f17])).
% 2.08/0.99  
% 2.08/0.99  fof(f84,plain,(
% 2.08/0.99    r1_tarski(sK4,sK5)),
% 2.08/0.99    inference(cnf_transformation,[],[f54])).
% 2.08/0.99  
% 2.08/0.99  fof(f9,axiom,(
% 2.08/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f32,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f9])).
% 2.08/0.99  
% 2.08/0.99  fof(f33,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f32])).
% 2.08/0.99  
% 2.08/0.99  fof(f78,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f33])).
% 2.08/0.99  
% 2.08/0.99  fof(f8,axiom,(
% 2.08/0.99    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f30,plain,(
% 2.08/0.99    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f8])).
% 2.08/0.99  
% 2.08/0.99  fof(f31,plain,(
% 2.08/0.99    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f30])).
% 2.08/0.99  
% 2.08/0.99  fof(f76,plain,(
% 2.08/0.99    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f31])).
% 2.08/0.99  
% 2.08/0.99  fof(f60,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f38])).
% 2.08/0.99  
% 2.08/0.99  fof(f65,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK0(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f42])).
% 2.08/0.99  
% 2.08/0.99  fof(f63,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f42])).
% 2.08/0.99  
% 2.08/0.99  fof(f62,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f42])).
% 2.08/0.99  
% 2.08/0.99  fof(f85,plain,(
% 2.08/0.99    ~r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4)) | ~r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5))),
% 2.08/0.99    inference(cnf_transformation,[],[f54])).
% 2.08/0.99  
% 2.08/0.99  fof(f10,axiom,(
% 2.08/0.99    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f34,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f10])).
% 2.08/0.99  
% 2.08/0.99  fof(f35,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f34])).
% 2.08/0.99  
% 2.08/0.99  fof(f79,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f35])).
% 2.08/0.99  
% 2.08/0.99  fof(f5,axiom,(
% 2.08/0.99    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f24,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f5])).
% 2.08/0.99  
% 2.08/0.99  fof(f25,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f24])).
% 2.08/0.99  
% 2.08/0.99  fof(f43,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(nnf_transformation,[],[f25])).
% 2.08/0.99  
% 2.08/0.99  fof(f44,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(rectify,[],[f43])).
% 2.08/0.99  
% 2.08/0.99  fof(f45,plain,(
% 2.08/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f46,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 2.08/0.99  
% 2.08/0.99  fof(f68,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f46])).
% 2.08/0.99  
% 2.08/0.99  fof(f70,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f51])).
% 2.08/0.99  
% 2.08/0.99  fof(f87,plain,(
% 2.08/0.99    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(equality_resolution,[],[f70])).
% 2.08/0.99  
% 2.08/0.99  fof(f66,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f46])).
% 2.08/0.99  
% 2.08/0.99  fof(f69,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK1(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f46])).
% 2.08/0.99  
% 2.08/0.99  fof(f67,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f46])).
% 2.08/0.99  
% 2.08/0.99  cnf(c_20,plain,
% 2.08/0.99      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_30,negated_conjecture,
% 2.08/0.99      ( ~ v2_struct_0(sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_718,plain,
% 2.08/0.99      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_719,plain,
% 2.08/0.99      ( m1_subset_1(k15_lattice3(sK3,X0),u1_struct_0(sK3))
% 2.08/0.99      | ~ l3_lattices(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_718]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_27,negated_conjecture,
% 2.08/0.99      ( l3_lattices(sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_723,plain,
% 2.08/0.99      ( m1_subset_1(k15_lattice3(sK3,X0),u1_struct_0(sK3)) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_719,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_18,plain,
% 2.08/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 2.08/0.99      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 2.08/0.99      | ~ v4_lattice3(X0)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_28,negated_conjecture,
% 2.08/0.99      ( v4_lattice3(sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_515,plain,
% 2.08/0.99      ( ~ r4_lattice3(X0,X1,X2)
% 2.08/0.99      | r1_lattices(X0,k15_lattice3(X0,X2),X1)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_516,plain,
% 2.08/0.99      ( ~ r4_lattice3(sK3,X0,X1)
% 2.08/0.99      | r1_lattices(sK3,k15_lattice3(sK3,X1),X0)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(k15_lattice3(sK3,X1),u1_struct_0(sK3))
% 2.08/0.99      | ~ l3_lattices(sK3)
% 2.08/0.99      | v2_struct_0(sK3)
% 2.08/0.99      | ~ v10_lattices(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_515]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_29,negated_conjecture,
% 2.08/0.99      ( v10_lattices(sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_520,plain,
% 2.08/0.99      ( ~ m1_subset_1(k15_lattice3(sK3,X1),u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | r1_lattices(sK3,k15_lattice3(sK3,X1),X0)
% 2.08/0.99      | ~ r4_lattice3(sK3,X0,X1) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_516,c_30,c_29,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_521,plain,
% 2.08/0.99      ( ~ r4_lattice3(sK3,X0,X1)
% 2.08/0.99      | r1_lattices(sK3,k15_lattice3(sK3,X1),X0)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(k15_lattice3(sK3,X1),u1_struct_0(sK3)) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_520]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_916,plain,
% 2.08/0.99      ( ~ r4_lattice3(sK3,X0,X1)
% 2.08/0.99      | r1_lattices(sK3,k15_lattice3(sK3,X1),X0)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_723,c_521]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2078,plain,
% 2.08/0.99      ( ~ r4_lattice3(sK3,X0_52,X0_53)
% 2.08/0.99      | r1_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52)
% 2.08/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_916]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2555,plain,
% 2.08/0.99      ( r4_lattice3(sK3,X0_52,X0_53) != iProver_top
% 2.08/0.99      | r1_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2078]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2087,plain,
% 2.08/0.99      ( m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_723]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2546,plain,
% 2.08/0.99      ( m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2087]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1,plain,
% 2.08/0.99      ( ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0)
% 2.08/0.99      | v9_lattices(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_5,plain,
% 2.08/0.99      ( ~ r1_lattices(X0,X1,X2)
% 2.08/0.99      | r3_lattices(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ v6_lattices(X0)
% 2.08/0.99      | ~ v8_lattices(X0)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v9_lattices(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_389,plain,
% 2.08/0.99      ( ~ r1_lattices(X0,X1,X2)
% 2.08/0.99      | r3_lattices(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ v6_lattices(X0)
% 2.08/0.99      | ~ v8_lattices(X0)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0) ),
% 2.08/0.99      inference(resolution,[status(thm)],[c_1,c_5]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3,plain,
% 2.08/0.99      ( v6_lattices(X0)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2,plain,
% 2.08/0.99      ( v8_lattices(X0)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_393,plain,
% 2.08/0.99      ( ~ r1_lattices(X0,X1,X2)
% 2.08/0.99      | r3_lattices(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_389,c_3,c_2]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_645,plain,
% 2.08/0.99      ( ~ r1_lattices(X0,X1,X2)
% 2.08/0.99      | r3_lattices(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_393,c_29]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_646,plain,
% 2.08/0.99      ( ~ r1_lattices(sK3,X0,X1)
% 2.08/0.99      | r3_lattices(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.08/0.99      | ~ l3_lattices(sK3)
% 2.08/0.99      | v2_struct_0(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_645]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_650,plain,
% 2.08/0.99      ( ~ r1_lattices(sK3,X0,X1)
% 2.08/0.99      | r3_lattices(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_646,c_30,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_651,plain,
% 2.08/0.99      ( ~ r1_lattices(sK3,X0,X1)
% 2.08/0.99      | r3_lattices(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_650]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2090,plain,
% 2.08/0.99      ( ~ r1_lattices(sK3,X0_52,X1_52)
% 2.08/0.99      | r3_lattices(sK3,X0_52,X1_52)
% 2.08/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X1_52,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_651]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2543,plain,
% 2.08/0.99      ( r1_lattices(sK3,X0_52,X1_52) != iProver_top
% 2.08/0.99      | r3_lattices(sK3,X0_52,X1_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | m1_subset_1(X1_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2090]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3474,plain,
% 2.08/0.99      ( r1_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52) != iProver_top
% 2.08/0.99      | r3_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2546,c_2543]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_4025,plain,
% 2.08/0.99      ( r4_lattice3(sK3,X0_52,X0_53) != iProver_top
% 2.08/0.99      | r3_lattices(sK3,k15_lattice3(sK3,X0_53),X0_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2555,c_3474]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_8,plain,
% 2.08/0.99      ( r3_lattice3(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_871,plain,
% 2.08/0.99      ( r3_lattice3(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_30]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_872,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | r2_hidden(sK0(sK3,X0,X1),X1)
% 2.08/0.99      | ~ l3_lattices(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_871]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_876,plain,
% 2.08/0.99      ( r2_hidden(sK0(sK3,X0,X1),X1)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | r3_lattice3(sK3,X0,X1) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_872,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_877,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | r2_hidden(sK0(sK3,X0,X1),X1) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_876]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2080,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0_52,X0_53)
% 2.08/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.08/0.99      | r2_hidden(sK0(sK3,X0_52,X0_53),X0_53) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_877]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2553,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0_52,X0_53) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(sK0(sK3,X0_52,X0_53),X0_53) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2080]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_0,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_26,negated_conjecture,
% 2.08/0.99      ( r1_tarski(sK4,sK5) ),
% 2.08/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_342,plain,
% 2.08/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | sK4 != X1 | sK5 != X2 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_26]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_343,plain,
% 2.08/0.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(X0,sK5) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_342]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2098,plain,
% 2.08/0.99      ( ~ r2_hidden(X0_52,sK4) | r2_hidden(X0_52,sK5) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_343]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2535,plain,
% 2.08/0.99      ( r2_hidden(X0_52,sK4) != iProver_top
% 2.08/0.99      | r2_hidden(X0_52,sK5) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2098]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3754,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0_52,sK4) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(sK0(sK3,X0_52,sK4),sK5) = iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2553,c_2535]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_22,plain,
% 2.08/0.99      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ r2_hidden(X2,X1)
% 2.08/0.99      | ~ v4_lattice3(X0)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_494,plain,
% 2.08/0.99      ( r3_lattices(X0,k16_lattice3(X0,X1),X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ r2_hidden(X2,X1)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_495,plain,
% 2.08/0.99      ( r3_lattices(sK3,k16_lattice3(sK3,X0),X1)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.08/0.99      | ~ r2_hidden(X1,X0)
% 2.08/0.99      | ~ l3_lattices(sK3)
% 2.08/0.99      | v2_struct_0(sK3)
% 2.08/0.99      | ~ v10_lattices(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_494]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_499,plain,
% 2.08/0.99      ( ~ r2_hidden(X1,X0)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.08/0.99      | r3_lattices(sK3,k16_lattice3(sK3,X0),X1) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_495,c_30,c_29,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_500,plain,
% 2.08/0.99      ( r3_lattices(sK3,k16_lattice3(sK3,X0),X1)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.08/0.99      | ~ r2_hidden(X1,X0) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_499]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2094,plain,
% 2.08/0.99      ( r3_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52)
% 2.08/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.08/0.99      | ~ r2_hidden(X0_52,X0_53) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_500]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2539,plain,
% 2.08/0.99      ( r3_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(X0_52,X0_53) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2094]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_21,plain,
% 2.08/0.99      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_703,plain,
% 2.08/0.99      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_704,plain,
% 2.08/0.99      ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3))
% 2.08/0.99      | ~ l3_lattices(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_703]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_708,plain,
% 2.08/0.99      ( m1_subset_1(k16_lattice3(sK3,X0),u1_struct_0(sK3)) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_704,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2088,plain,
% 2.08/0.99      ( m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_708]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2545,plain,
% 2.08/0.99      ( m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2088]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_6,plain,
% 2.08/0.99      ( r1_lattices(X0,X1,X2)
% 2.08/0.99      | ~ r3_lattices(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ v6_lattices(X0)
% 2.08/0.99      | ~ v8_lattices(X0)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v9_lattices(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_357,plain,
% 2.08/0.99      ( r1_lattices(X0,X1,X2)
% 2.08/0.99      | ~ r3_lattices(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ v6_lattices(X0)
% 2.08/0.99      | ~ v8_lattices(X0)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0) ),
% 2.08/0.99      inference(resolution,[status(thm)],[c_1,c_6]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_361,plain,
% 2.08/0.99      ( r1_lattices(X0,X1,X2)
% 2.08/0.99      | ~ r3_lattices(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_357,c_3,c_2]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_669,plain,
% 2.08/0.99      ( r1_lattices(X0,X1,X2)
% 2.08/0.99      | ~ r3_lattices(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_361,c_29]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_670,plain,
% 2.08/0.99      ( r1_lattices(sK3,X0,X1)
% 2.08/0.99      | ~ r3_lattices(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.08/0.99      | ~ l3_lattices(sK3)
% 2.08/0.99      | v2_struct_0(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_669]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_674,plain,
% 2.08/0.99      ( r1_lattices(sK3,X0,X1)
% 2.08/0.99      | ~ r3_lattices(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_670,c_30,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_675,plain,
% 2.08/0.99      ( r1_lattices(sK3,X0,X1)
% 2.08/0.99      | ~ r3_lattices(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_674]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2089,plain,
% 2.08/0.99      ( r1_lattices(sK3,X0_52,X1_52)
% 2.08/0.99      | ~ r3_lattices(sK3,X0_52,X1_52)
% 2.08/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X1_52,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_675]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2544,plain,
% 2.08/0.99      ( r1_lattices(sK3,X0_52,X1_52) = iProver_top
% 2.08/0.99      | r3_lattices(sK3,X0_52,X1_52) != iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | m1_subset_1(X1_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2089]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3540,plain,
% 2.08/0.99      ( r1_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
% 2.08/0.99      | r3_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) != iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2545,c_2544]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_4077,plain,
% 2.08/0.99      ( r1_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(X0_52,X0_53) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2539,c_3540]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_7,plain,
% 2.08/0.99      ( r3_lattice3(X0,X1,X2)
% 2.08/0.99      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_892,plain,
% 2.08/0.99      ( r3_lattice3(X0,X1,X2)
% 2.08/0.99      | ~ r1_lattices(X0,X1,sK0(X0,X1,X2))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_30]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_893,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ l3_lattices(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_892]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_897,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
% 2.08/0.99      | r3_lattice3(sK3,X0,X1) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_893,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_898,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | ~ r1_lattices(sK3,X0,sK0(sK3,X0,X1))
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_897]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2079,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0_52,X0_53)
% 2.08/0.99      | ~ r1_lattices(sK3,X0_52,sK0(sK3,X0_52,X0_53))
% 2.08/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_898]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2554,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0_52,X0_53) = iProver_top
% 2.08/0.99      | r1_lattices(sK3,X0_52,sK0(sK3,X0_52,X0_53)) != iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2079]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_4322,plain,
% 2.08/0.99      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53) = iProver_top
% 2.08/0.99      | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),X0_53) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_4077,c_2554]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2146,plain,
% 2.08/0.99      ( m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2088]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_9,plain,
% 2.08/0.99      ( r3_lattice3(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_850,plain,
% 2.08/0.99      ( r3_lattice3(X0,X1,X2)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_851,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
% 2.08/0.99      | ~ l3_lattices(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_850]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_855,plain,
% 2.08/0.99      ( m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | r3_lattice3(sK3,X0,X1) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_851,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_856,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_855]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2081,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0_52,X0_53)
% 2.08/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.08/0.99      | m1_subset_1(sK0(sK3,X0_52,X0_53),u1_struct_0(sK3)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_856]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2744,plain,
% 2.08/0.99      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53)
% 2.08/0.99      | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_2081]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2745,plain,
% 2.08/0.99      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53) = iProver_top
% 2.08/0.99      | m1_subset_1(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3)) = iProver_top
% 2.08/0.99      | m1_subset_1(k16_lattice3(sK3,X0_53),u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2744]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_5106,plain,
% 2.08/0.99      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53) = iProver_top
% 2.08/0.99      | r2_hidden(sK0(sK3,k16_lattice3(sK3,X0_53),X1_53),X0_53) != iProver_top ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_4322,c_2146,c_2745]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_5115,plain,
% 2.08/0.99      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) = iProver_top
% 2.08/0.99      | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_3754,c_5106]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_4033,plain,
% 2.08/0.99      ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_2088]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_4034,plain,
% 2.08/0.99      ( m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_4033]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_5356,plain,
% 2.08/0.99      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) = iProver_top ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5115,c_4034]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_10,plain,
% 2.08/0.99      ( ~ r3_lattice3(X0,X1,X2)
% 2.08/0.99      | r1_lattices(X0,X1,X3)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.08/0.99      | ~ r2_hidden(X3,X2)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_823,plain,
% 2.08/0.99      ( ~ r3_lattice3(X0,X1,X2)
% 2.08/0.99      | r1_lattices(X0,X1,X3)
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.08/0.99      | ~ r2_hidden(X3,X2)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_824,plain,
% 2.08/0.99      ( ~ r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | r1_lattices(sK3,X0,X2)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.08/0.99      | ~ r2_hidden(X2,X1)
% 2.08/0.99      | ~ l3_lattices(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_823]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_828,plain,
% 2.08/0.99      ( ~ r2_hidden(X2,X1)
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | r1_lattices(sK3,X0,X2)
% 2.08/0.99      | ~ r3_lattice3(sK3,X0,X1) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_824,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_829,plain,
% 2.08/0.99      ( ~ r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | r1_lattices(sK3,X0,X2)
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.08/0.99      | ~ r2_hidden(X2,X1) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_828]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2082,plain,
% 2.08/0.99      ( ~ r3_lattice3(sK3,X0_52,X0_53)
% 2.08/0.99      | r1_lattices(sK3,X0_52,X1_52)
% 2.08/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.08/0.99      | ~ m1_subset_1(X1_52,u1_struct_0(sK3))
% 2.08/0.99      | ~ r2_hidden(X1_52,X0_53) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_829]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2551,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0_52,X0_53) != iProver_top
% 2.08/0.99      | r1_lattices(sK3,X0_52,X1_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | m1_subset_1(X1_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(X1_52,X0_53) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2082]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3640,plain,
% 2.08/0.99      ( r3_lattice3(sK3,k16_lattice3(sK3,X0_53),X1_53) != iProver_top
% 2.08/0.99      | r1_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(X0_52,X1_53) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2545,c_2551]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_5361,plain,
% 2.08/0.99      ( r1_lattices(sK3,k16_lattice3(sK3,sK5),X0_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(X0_52,sK4) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_5356,c_3640]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3475,plain,
% 2.08/0.99      ( r1_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) != iProver_top
% 2.08/0.99      | r3_lattices(sK3,k16_lattice3(sK3,X0_53),X0_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2545,c_2543]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_5435,plain,
% 2.08/0.99      ( r3_lattices(sK3,k16_lattice3(sK3,sK5),X0_52) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(X0_52,sK4) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_5361,c_3475]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_25,negated_conjecture,
% 2.08/0.99      ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
% 2.08/0.99      | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
% 2.08/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2099,negated_conjecture,
% 2.08/0.99      ( ~ r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4))
% 2.08/0.99      | ~ r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2534,plain,
% 2.08/0.99      ( r3_lattices(sK3,k16_lattice3(sK3,sK5),k16_lattice3(sK3,sK4)) != iProver_top
% 2.08/0.99      | r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2099]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_6259,plain,
% 2.08/0.99      ( r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top
% 2.08/0.99      | m1_subset_1(k16_lattice3(sK3,sK4),u1_struct_0(sK3)) != iProver_top
% 2.08/0.99      | r2_hidden(k16_lattice3(sK3,sK4),sK4) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_5435,c_2534]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_24,plain,
% 2.08/0.99      ( ~ r3_lattice3(X0,X1,X2)
% 2.08/0.99      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ v4_lattice3(X0)
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_452,plain,
% 2.08/0.99      ( ~ r3_lattice3(X0,X1,X2)
% 2.08/0.99      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
% 2.08/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/0.99      | ~ l3_lattices(X0)
% 2.08/0.99      | v2_struct_0(X0)
% 2.08/0.99      | ~ v10_lattices(X0)
% 2.08/0.99      | sK3 != X0 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_453,plain,
% 2.08/0.99      ( ~ r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | ~ l3_lattices(sK3)
% 2.08/0.99      | v2_struct_0(sK3)
% 2.08/0.99      | ~ v10_lattices(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_452]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_457,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/0.99      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 2.08/0.99      | ~ r3_lattice3(sK3,X0,X1) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_453,c_30,c_29,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_458,plain,
% 2.08/0.99      ( ~ r3_lattice3(sK3,X0,X1)
% 2.08/0.99      | r3_lattices(sK3,X0,k16_lattice3(sK3,X1))
% 2.08/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_457]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2096,plain,
% 2.08/0.99      ( ~ r3_lattice3(sK3,X0_52,X0_53)
% 2.08/0.99      | r3_lattices(sK3,X0_52,k16_lattice3(sK3,X0_53))
% 2.08/0.99      | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_458]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2537,plain,
% 2.08/0.99      ( r3_lattice3(sK3,X0_52,X0_53) != iProver_top
% 2.08/0.99      | r3_lattices(sK3,X0_52,k16_lattice3(sK3,X0_53)) = iProver_top
% 2.08/0.99      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_2096]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3052,plain,
% 2.08/0.99      ( r3_lattice3(sK3,k16_lattice3(sK3,sK5),sK4) != iProver_top
% 2.08/0.99      | r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top
% 2.08/0.99      | m1_subset_1(k16_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2537,c_2534]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_6316,plain,
% 2.08/0.99      ( r3_lattices(sK3,k15_lattice3(sK3,sK4),k15_lattice3(sK3,sK5)) != iProver_top ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_6259,c_3052,c_4034,c_5115]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_6326,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,sK5),sK4) != iProver_top
% 2.08/1.00      | m1_subset_1(k15_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
% 2.08/1.00      inference(superposition,[status(thm)],[c_4025,c_6316]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_12,plain,
% 2.08/1.00      ( r4_lattice3(X0,X1,X2)
% 2.08/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | v2_struct_0(X0) ),
% 2.08/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_781,plain,
% 2.08/1.00      ( r4_lattice3(X0,X1,X2)
% 2.08/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | sK3 != X0 ),
% 2.08/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_782,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0,X1)
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | r2_hidden(sK1(sK3,X0,X1),X1)
% 2.08/1.00      | ~ l3_lattices(sK3) ),
% 2.08/1.00      inference(unflattening,[status(thm)],[c_781]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_786,plain,
% 2.08/1.00      ( r2_hidden(sK1(sK3,X0,X1),X1)
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | r4_lattice3(sK3,X0,X1) ),
% 2.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_782,c_27]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_787,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0,X1)
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | r2_hidden(sK1(sK3,X0,X1),X1) ),
% 2.08/1.00      inference(renaming,[status(thm)],[c_786]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2084,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0_52,X0_53)
% 2.08/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.08/1.00      | r2_hidden(sK1(sK3,X0_52,X0_53),X0_53) ),
% 2.08/1.00      inference(subtyping,[status(esa)],[c_787]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2549,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0_52,X0_53) = iProver_top
% 2.08/1.00      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/1.00      | r2_hidden(sK1(sK3,X0_52,X0_53),X0_53) = iProver_top ),
% 2.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2084]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_3707,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0_52,sK4) = iProver_top
% 2.08/1.00      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/1.00      | r2_hidden(sK1(sK3,X0_52,sK4),sK5) = iProver_top ),
% 2.08/1.00      inference(superposition,[status(thm)],[c_2549,c_2535]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_19,plain,
% 2.08/1.00      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 2.08/1.00      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
% 2.08/1.00      | ~ v4_lattice3(X0)
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | v2_struct_0(X0)
% 2.08/1.00      | ~ v10_lattices(X0) ),
% 2.08/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_182,plain,
% 2.08/1.00      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 2.08/1.00      | ~ v4_lattice3(X0)
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | v2_struct_0(X0)
% 2.08/1.00      | ~ v10_lattices(X0) ),
% 2.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_19,c_20]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_437,plain,
% 2.08/1.00      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | v2_struct_0(X0)
% 2.08/1.00      | ~ v10_lattices(X0)
% 2.08/1.00      | sK3 != X0 ),
% 2.08/1.00      inference(resolution_lifted,[status(thm)],[c_182,c_28]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_438,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,X0),X0)
% 2.08/1.00      | ~ l3_lattices(sK3)
% 2.08/1.00      | v2_struct_0(sK3)
% 2.08/1.00      | ~ v10_lattices(sK3) ),
% 2.08/1.00      inference(unflattening,[status(thm)],[c_437]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_442,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,X0),X0) ),
% 2.08/1.00      inference(global_propositional_subsumption,
% 2.08/1.00                [status(thm)],
% 2.08/1.00                [c_438,c_30,c_29,c_27]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2097,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X0_53) ),
% 2.08/1.00      inference(subtyping,[status(esa)],[c_442]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2536,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X0_53) = iProver_top ),
% 2.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2097]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_14,plain,
% 2.08/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 2.08/1.00      | r1_lattices(X0,X3,X1)
% 2.08/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.08/1.00      | ~ r2_hidden(X3,X2)
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | v2_struct_0(X0) ),
% 2.08/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_733,plain,
% 2.08/1.00      ( ~ r4_lattice3(X0,X1,X2)
% 2.08/1.00      | r1_lattices(X0,X3,X1)
% 2.08/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.08/1.00      | ~ r2_hidden(X3,X2)
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | sK3 != X0 ),
% 2.08/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_734,plain,
% 2.08/1.00      ( ~ r4_lattice3(sK3,X0,X1)
% 2.08/1.00      | r1_lattices(sK3,X2,X0)
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.08/1.00      | ~ r2_hidden(X2,X1)
% 2.08/1.00      | ~ l3_lattices(sK3) ),
% 2.08/1.00      inference(unflattening,[status(thm)],[c_733]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_738,plain,
% 2.08/1.00      ( ~ r2_hidden(X2,X1)
% 2.08/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | r1_lattices(sK3,X2,X0)
% 2.08/1.00      | ~ r4_lattice3(sK3,X0,X1) ),
% 2.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_734,c_27]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_739,plain,
% 2.08/1.00      ( ~ r4_lattice3(sK3,X0,X1)
% 2.08/1.00      | r1_lattices(sK3,X2,X0)
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 2.08/1.00      | ~ r2_hidden(X2,X1) ),
% 2.08/1.00      inference(renaming,[status(thm)],[c_738]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2086,plain,
% 2.08/1.00      ( ~ r4_lattice3(sK3,X0_52,X0_53)
% 2.08/1.00      | r1_lattices(sK3,X1_52,X0_52)
% 2.08/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.08/1.00      | ~ m1_subset_1(X1_52,u1_struct_0(sK3))
% 2.08/1.00      | ~ r2_hidden(X1_52,X0_53) ),
% 2.08/1.00      inference(subtyping,[status(esa)],[c_739]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2547,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0_52,X0_53) != iProver_top
% 2.08/1.00      | r1_lattices(sK3,X1_52,X0_52) = iProver_top
% 2.08/1.00      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/1.00      | m1_subset_1(X1_52,u1_struct_0(sK3)) != iProver_top
% 2.08/1.00      | r2_hidden(X1_52,X0_53) != iProver_top ),
% 2.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2086]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_3591,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53) != iProver_top
% 2.08/1.00      | r1_lattices(sK3,X0_52,k15_lattice3(sK3,X0_53)) = iProver_top
% 2.08/1.00      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/1.00      | r2_hidden(X0_52,X1_53) != iProver_top ),
% 2.08/1.00      inference(superposition,[status(thm)],[c_2546,c_2547]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_4354,plain,
% 2.08/1.00      ( r1_lattices(sK3,X0_52,k15_lattice3(sK3,X0_53)) = iProver_top
% 2.08/1.00      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top
% 2.08/1.00      | r2_hidden(X0_52,X0_53) != iProver_top ),
% 2.08/1.00      inference(superposition,[status(thm)],[c_2536,c_3591]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_11,plain,
% 2.08/1.00      ( r4_lattice3(X0,X1,X2)
% 2.08/1.00      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 2.08/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | v2_struct_0(X0) ),
% 2.08/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_802,plain,
% 2.08/1.00      ( r4_lattice3(X0,X1,X2)
% 2.08/1.00      | ~ r1_lattices(X0,sK1(X0,X1,X2),X1)
% 2.08/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | sK3 != X0 ),
% 2.08/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_30]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_803,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0,X1)
% 2.08/1.00      | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | ~ l3_lattices(sK3) ),
% 2.08/1.00      inference(unflattening,[status(thm)],[c_802]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_807,plain,
% 2.08/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
% 2.08/1.00      | r4_lattice3(sK3,X0,X1) ),
% 2.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_803,c_27]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_808,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0,X1)
% 2.08/1.00      | ~ r1_lattices(sK3,sK1(sK3,X0,X1),X0)
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.08/1.00      inference(renaming,[status(thm)],[c_807]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2083,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0_52,X0_53)
% 2.08/1.00      | ~ r1_lattices(sK3,sK1(sK3,X0_52,X0_53),X0_52)
% 2.08/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3)) ),
% 2.08/1.00      inference(subtyping,[status(esa)],[c_808]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2550,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0_52,X0_53) = iProver_top
% 2.08/1.00      | r1_lattices(sK3,sK1(sK3,X0_52,X0_53),X0_52) != iProver_top
% 2.08/1.00      | m1_subset_1(X0_52,u1_struct_0(sK3)) != iProver_top ),
% 2.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2083]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_4409,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53) = iProver_top
% 2.08/1.00      | m1_subset_1(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3)) != iProver_top
% 2.08/1.00      | m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) != iProver_top
% 2.08/1.00      | r2_hidden(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),X0_53) != iProver_top ),
% 2.08/1.00      inference(superposition,[status(thm)],[c_4354,c_2550]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2149,plain,
% 2.08/1.00      ( m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) = iProver_top ),
% 2.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2087]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_13,plain,
% 2.08/1.00      ( r4_lattice3(X0,X1,X2)
% 2.08/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | v2_struct_0(X0) ),
% 2.08/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_760,plain,
% 2.08/1.00      ( r4_lattice3(X0,X1,X2)
% 2.08/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.08/1.00      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 2.08/1.00      | ~ l3_lattices(X0)
% 2.08/1.00      | sK3 != X0 ),
% 2.08/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_761,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0,X1)
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
% 2.08/1.00      | ~ l3_lattices(sK3) ),
% 2.08/1.00      inference(unflattening,[status(thm)],[c_760]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_765,plain,
% 2.08/1.00      ( m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3))
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | r4_lattice3(sK3,X0,X1) ),
% 2.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_761,c_27]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_766,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0,X1)
% 2.08/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.08/1.00      | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
% 2.08/1.00      inference(renaming,[status(thm)],[c_765]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2085,plain,
% 2.08/1.00      ( r4_lattice3(sK3,X0_52,X0_53)
% 2.08/1.00      | ~ m1_subset_1(X0_52,u1_struct_0(sK3))
% 2.08/1.00      | m1_subset_1(sK1(sK3,X0_52,X0_53),u1_struct_0(sK3)) ),
% 2.08/1.00      inference(subtyping,[status(esa)],[c_766]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2749,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53)
% 2.08/1.00      | m1_subset_1(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3))
% 2.08/1.00      | ~ m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) ),
% 2.08/1.00      inference(instantiation,[status(thm)],[c_2085]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_2750,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53) = iProver_top
% 2.08/1.00      | m1_subset_1(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),u1_struct_0(sK3)) = iProver_top
% 2.08/1.00      | m1_subset_1(k15_lattice3(sK3,X0_53),u1_struct_0(sK3)) != iProver_top ),
% 2.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2749]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_5206,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,X0_53),X1_53) = iProver_top
% 2.08/1.00      | r2_hidden(sK1(sK3,k15_lattice3(sK3,X0_53),X1_53),X0_53) != iProver_top ),
% 2.08/1.00      inference(global_propositional_subsumption,
% 2.08/1.00                [status(thm)],
% 2.08/1.00                [c_4409,c_2149,c_2750]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_5213,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,sK5),sK4) = iProver_top
% 2.08/1.00      | m1_subset_1(k15_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
% 2.08/1.00      inference(superposition,[status(thm)],[c_3707,c_5206]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_5378,plain,
% 2.08/1.00      ( r4_lattice3(sK3,k15_lattice3(sK3,sK5),sK4) = iProver_top ),
% 2.08/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5213,c_2546]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_6349,plain,
% 2.08/1.00      ( m1_subset_1(k15_lattice3(sK3,sK5),u1_struct_0(sK3)) != iProver_top ),
% 2.08/1.00      inference(global_propositional_subsumption,[status(thm)],[c_6326,c_5378]) ).
% 2.08/1.00  
% 2.08/1.00  cnf(c_6354,plain,
% 2.08/1.00      ( $false ),
% 2.08/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_6349,c_2546]) ).
% 2.08/1.00  
% 2.08/1.00  
% 2.08/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/1.00  
% 2.08/1.00  ------                               Statistics
% 2.08/1.00  
% 2.08/1.00  ------ General
% 2.08/1.00  
% 2.08/1.00  abstr_ref_over_cycles:                  0
% 2.08/1.00  abstr_ref_under_cycles:                 0
% 2.08/1.00  gc_basic_clause_elim:                   0
% 2.08/1.00  forced_gc_time:                         0
% 2.08/1.00  parsing_time:                           0.008
% 2.08/1.00  unif_index_cands_time:                  0.
% 2.08/1.00  unif_index_add_time:                    0.
% 2.08/1.00  orderings_time:                         0.
% 2.08/1.00  out_proof_time:                         0.014
% 2.08/1.00  total_time:                             0.198
% 2.08/1.00  num_of_symbols:                         55
% 2.08/1.00  num_of_terms:                           5106
% 2.08/1.00  
% 2.08/1.00  ------ Preprocessing
% 2.08/1.00  
% 2.08/1.00  num_of_splits:                          0
% 2.08/1.00  num_of_split_atoms:                     0
% 2.08/1.00  num_of_reused_defs:                     0
% 2.08/1.00  num_eq_ax_congr_red:                    52
% 2.08/1.00  num_of_sem_filtered_clauses:            1
% 2.08/1.00  num_of_subtypes:                        4
% 2.08/1.00  monotx_restored_types:                  0
% 2.08/1.00  sat_num_of_epr_types:                   0
% 2.08/1.00  sat_num_of_non_cyclic_types:            0
% 2.08/1.00  sat_guarded_non_collapsed_types:        1
% 2.08/1.00  num_pure_diseq_elim:                    0
% 2.08/1.00  simp_replaced_by:                       0
% 2.08/1.00  res_preprocessed:                       111
% 2.08/1.00  prep_upred:                             0
% 2.08/1.00  prep_unflattend:                        80
% 2.08/1.00  smt_new_axioms:                         0
% 2.08/1.00  pred_elim_cands:                        6
% 2.08/1.00  pred_elim:                              8
% 2.08/1.00  pred_elim_cl:                           8
% 2.08/1.00  pred_elim_cycles:                       12
% 2.08/1.00  merged_defs:                            0
% 2.08/1.00  merged_defs_ncl:                        0
% 2.08/1.00  bin_hyper_res:                          0
% 2.08/1.00  prep_cycles:                            4
% 2.08/1.00  pred_elim_time:                         0.028
% 2.08/1.00  splitting_time:                         0.
% 2.08/1.00  sem_filter_time:                        0.
% 2.08/1.00  monotx_time:                            0.
% 2.08/1.00  subtype_inf_time:                       0.
% 2.08/1.00  
% 2.08/1.00  ------ Problem properties
% 2.08/1.00  
% 2.08/1.00  clauses:                                22
% 2.08/1.00  conjectures:                            1
% 2.08/1.00  epr:                                    1
% 2.08/1.00  horn:                                   16
% 2.08/1.00  ground:                                 1
% 2.08/1.00  unary:                                  3
% 2.08/1.00  binary:                                 2
% 2.08/1.00  lits:                                   67
% 2.08/1.00  lits_eq:                                3
% 2.08/1.00  fd_pure:                                0
% 2.08/1.00  fd_pseudo:                              0
% 2.08/1.00  fd_cond:                                0
% 2.08/1.00  fd_pseudo_cond:                         3
% 2.08/1.00  ac_symbols:                             0
% 2.08/1.00  
% 2.08/1.00  ------ Propositional Solver
% 2.08/1.00  
% 2.08/1.00  prop_solver_calls:                      27
% 2.08/1.00  prop_fast_solver_calls:                 1543
% 2.08/1.00  smt_solver_calls:                       0
% 2.08/1.00  smt_fast_solver_calls:                  0
% 2.08/1.00  prop_num_of_clauses:                    2481
% 2.08/1.00  prop_preprocess_simplified:             6241
% 2.08/1.00  prop_fo_subsumed:                       89
% 2.08/1.00  prop_solver_time:                       0.
% 2.08/1.00  smt_solver_time:                        0.
% 2.08/1.00  smt_fast_solver_time:                   0.
% 2.08/1.00  prop_fast_solver_time:                  0.
% 2.08/1.00  prop_unsat_core_time:                   0.
% 2.08/1.00  
% 2.08/1.00  ------ QBF
% 2.08/1.00  
% 2.08/1.00  qbf_q_res:                              0
% 2.08/1.00  qbf_num_tautologies:                    0
% 2.08/1.00  qbf_prep_cycles:                        0
% 2.08/1.00  
% 2.08/1.00  ------ BMC1
% 2.08/1.00  
% 2.08/1.00  bmc1_current_bound:                     -1
% 2.08/1.00  bmc1_last_solved_bound:                 -1
% 2.08/1.00  bmc1_unsat_core_size:                   -1
% 2.08/1.00  bmc1_unsat_core_parents_size:           -1
% 2.08/1.00  bmc1_merge_next_fun:                    0
% 2.08/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.08/1.00  
% 2.08/1.00  ------ Instantiation
% 2.08/1.00  
% 2.08/1.00  inst_num_of_clauses:                    474
% 2.08/1.00  inst_num_in_passive:                    34
% 2.08/1.00  inst_num_in_active:                     279
% 2.08/1.00  inst_num_in_unprocessed:                161
% 2.08/1.00  inst_num_of_loops:                      330
% 2.08/1.00  inst_num_of_learning_restarts:          0
% 2.08/1.00  inst_num_moves_active_passive:          48
% 2.08/1.00  inst_lit_activity:                      0
% 2.08/1.00  inst_lit_activity_moves:                0
% 2.08/1.00  inst_num_tautologies:                   0
% 2.08/1.00  inst_num_prop_implied:                  0
% 2.08/1.00  inst_num_existing_simplified:           0
% 2.08/1.00  inst_num_eq_res_simplified:             0
% 2.08/1.00  inst_num_child_elim:                    0
% 2.08/1.00  inst_num_of_dismatching_blockings:      78
% 2.08/1.00  inst_num_of_non_proper_insts:           292
% 2.08/1.00  inst_num_of_duplicates:                 0
% 2.08/1.00  inst_inst_num_from_inst_to_res:         0
% 2.08/1.00  inst_dismatching_checking_time:         0.
% 2.08/1.00  
% 2.08/1.00  ------ Resolution
% 2.08/1.00  
% 2.08/1.00  res_num_of_clauses:                     0
% 2.08/1.00  res_num_in_passive:                     0
% 2.08/1.00  res_num_in_active:                      0
% 2.08/1.00  res_num_of_loops:                       115
% 2.08/1.00  res_forward_subset_subsumed:            11
% 2.08/1.00  res_backward_subset_subsumed:           0
% 2.08/1.00  res_forward_subsumed:                   0
% 2.08/1.00  res_backward_subsumed:                  0
% 2.08/1.00  res_forward_subsumption_resolution:     5
% 2.08/1.00  res_backward_subsumption_resolution:    1
% 2.08/1.00  res_clause_to_clause_subsumption:       305
% 2.08/1.00  res_orphan_elimination:                 0
% 2.08/1.00  res_tautology_del:                      24
% 2.08/1.00  res_num_eq_res_simplified:              0
% 2.08/1.00  res_num_sel_changes:                    0
% 2.08/1.00  res_moves_from_active_to_pass:          0
% 2.08/1.00  
% 2.08/1.00  ------ Superposition
% 2.08/1.00  
% 2.08/1.00  sup_time_total:                         0.
% 2.08/1.00  sup_time_generating:                    0.
% 2.08/1.00  sup_time_sim_full:                      0.
% 2.08/1.00  sup_time_sim_immed:                     0.
% 2.08/1.00  
% 2.08/1.00  sup_num_of_clauses:                     83
% 2.08/1.00  sup_num_in_active:                      63
% 2.08/1.00  sup_num_in_passive:                     20
% 2.08/1.00  sup_num_of_loops:                       64
% 2.08/1.00  sup_fw_superposition:                   34
% 2.08/1.00  sup_bw_superposition:                   41
% 2.08/1.00  sup_immediate_simplified:               7
% 2.08/1.00  sup_given_eliminated:                   0
% 2.08/1.00  comparisons_done:                       0
% 2.08/1.00  comparisons_avoided:                    0
% 2.08/1.00  
% 2.08/1.00  ------ Simplifications
% 2.08/1.00  
% 2.08/1.00  
% 2.08/1.00  sim_fw_subset_subsumed:                 2
% 2.08/1.00  sim_bw_subset_subsumed:                 1
% 2.08/1.00  sim_fw_subsumed:                        4
% 2.08/1.00  sim_bw_subsumed:                        1
% 2.08/1.00  sim_fw_subsumption_res:                 8
% 2.08/1.00  sim_bw_subsumption_res:                 0
% 2.08/1.00  sim_tautology_del:                      0
% 2.08/1.00  sim_eq_tautology_del:                   1
% 2.08/1.00  sim_eq_res_simp:                        0
% 2.08/1.00  sim_fw_demodulated:                     0
% 2.08/1.00  sim_bw_demodulated:                     0
% 2.08/1.00  sim_light_normalised:                   0
% 2.08/1.00  sim_joinable_taut:                      0
% 2.08/1.00  sim_joinable_simp:                      0
% 2.08/1.00  sim_ac_normalised:                      0
% 2.08/1.00  sim_smt_subsumption:                    0
% 2.08/1.00  
%------------------------------------------------------------------------------
