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
% DateTime   : Thu Dec  3 12:28:21 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 552 expanded)
%              Number of clauses        :   86 ( 134 expanded)
%              Number of leaves         :   13 ( 120 expanded)
%              Depth                    :   19
%              Number of atoms          :  687 (3613 expanded)
%              Number of equality atoms :   48 (  73 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK0(X0,X1,X2))
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK0(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK0(X0,X1,X2))
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
     => ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,sK4),k2_yellow_0(X0,sK3))
          | ~ r3_orders_2(X0,k1_yellow_0(X0,sK3),k1_yellow_0(X0,sK4)) )
        & r1_tarski(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r1_orders_2(sK2,k2_yellow_0(sK2,X2),k2_yellow_0(sK2,X1))
            | ~ r3_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK2)
      & v3_lattice3(sK2)
      & v1_lattice3(sK2)
      & v5_orders_2(sK2)
      & v3_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
      | ~ r3_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4)) )
    & r1_tarski(sK3,sK4)
    & l1_orders_2(sK2)
    & v3_lattice3(sK2)
    & v1_lattice3(sK2)
    & v5_orders_2(sK2)
    & v3_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f40,f39])).

fof(f64,plain,(
    v3_lattice3(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
        & r2_lattice3(X0,X1,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
                & r2_lattice3(X0,X1,sK1(X0,X1,X2))
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,
    ( ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
    | ~ r3_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_14])).

cnf(c_177,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_15,plain,
    ( r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( v3_lattice3(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_339,plain,
    ( r2_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_340,plain,
    ( r2_yellow_0(sK2,X0)
    | ~ v5_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_24,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( v1_lattice3(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2,plain,
    ( ~ v1_lattice3(X0)
    | ~ v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_78,plain,
    ( ~ v1_lattice3(sK2)
    | ~ v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_344,plain,
    ( r2_yellow_0(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_340,c_24,c_23,c_21,c_78])).

cnf(c_484,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_177,c_344])).

cnf(c_485,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ r1_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_21])).

cnf(c_490,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_489])).

cnf(c_920,plain,
    ( ~ r1_lattice3(sK2,X0_52,X0_51)
    | r1_orders_2(sK2,X0_51,k2_yellow_0(sK2,X0_52))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_490])).

cnf(c_1389,plain,
    ( ~ r1_lattice3(sK2,X0_52,k2_yellow_0(sK2,X1_52))
    | r1_orders_2(sK2,k2_yellow_0(sK2,X1_52),k2_yellow_0(sK2,X0_52))
    | ~ m1_subset_1(k2_yellow_0(sK2,X1_52),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_1614,plain,
    ( ~ r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
    | r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_11,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X1)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_13])).

cnf(c_160,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_159])).

cnf(c_16,plain,
    ( r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | ~ v3_lattice3(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_324,plain,
    ( r1_yellow_0(X0,X1)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_325,plain,
    ( r1_yellow_0(sK2,X0)
    | ~ v5_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_329,plain,
    ( r1_yellow_0(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_24,c_23,c_21,c_78])).

cnf(c_613,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_160,c_329])).

cnf(c_614,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ r2_lattice3(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_614,c_21])).

cnf(c_619,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_618])).

cnf(c_915,plain,
    ( ~ r2_lattice3(sK2,X0_52,X0_51)
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_619])).

cnf(c_1374,plain,
    ( ~ r2_lattice3(sK2,X0_52,k1_yellow_0(sK2,X1_52))
    | r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),k1_yellow_0(sK2,X1_52))
    | ~ m1_subset_1(k1_yellow_0(sK2,X1_52),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_1564,plain,
    ( ~ r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK4))
    | r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_772,plain,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_773,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_908,plain,
    ( m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_773])).

cnf(c_1536,plain,
    ( m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_12,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_152,plain,
    ( ~ r1_yellow_0(X0,X1)
    | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_13])).

cnf(c_153,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ r1_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_152])).

cnf(c_634,plain,
    ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | X2 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_153,c_329])).

cnf(c_635,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_639,plain,
    ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_21])).

cnf(c_914,plain,
    ( r2_lattice3(sK2,X0_52,k1_yellow_0(sK2,X0_52)) ),
    inference(subtyping,[status(esa)],[c_639])).

cnf(c_1369,plain,
    ( r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_17,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_376,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r2_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X3
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_377,plain,
    ( r2_lattice3(X0,sK3,X1)
    | ~ r2_lattice3(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_742,plain,
    ( r2_lattice3(X0,sK3,X1)
    | ~ r2_lattice3(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_377,c_21])).

cnf(c_743,plain,
    ( r2_lattice3(sK2,sK3,X0)
    | ~ r2_lattice3(sK2,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_910,plain,
    ( r2_lattice3(sK2,sK3,X0_51)
    | ~ r2_lattice3(sK2,sK4,X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_743])).

cnf(c_1368,plain,
    ( r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK4))
    | ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK4))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_169,plain,
    ( ~ r2_yellow_0(X0,X1)
    | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ l1_orders_2(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_14])).

cnf(c_170,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ r2_yellow_0(X0,X1)
    | ~ l1_orders_2(X0) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_505,plain,
    ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
    | ~ l1_orders_2(X0)
    | X2 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_170,c_344])).

cnf(c_506,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_510,plain,
    ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_21])).

cnf(c_919,plain,
    ( r1_lattice3(sK2,X0_52,k2_yellow_0(sK2,X0_52)) ),
    inference(subtyping,[status(esa)],[c_510])).

cnf(c_1363,plain,
    ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_18,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_358,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_lattice3(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | sK3 != X3
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_359,plain,
    ( r1_lattice3(X0,sK3,X1)
    | ~ r1_lattice3(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_757,plain,
    ( r1_lattice3(X0,sK3,X1)
    | ~ r1_lattice3(X0,sK4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_359,c_21])).

cnf(c_758,plain,
    ( r1_lattice3(sK2,sK3,X0)
    | ~ r1_lattice3(sK2,sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_909,plain,
    ( r1_lattice3(sK2,sK3,X0_51)
    | ~ r1_lattice3(sK2,sK4,X0_51)
    | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_758])).

cnf(c_1362,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
    | ~ r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4))
    | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_909])).

cnf(c_781,plain,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_782,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_907,plain,
    ( m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_782])).

cnf(c_1359,plain,
    ( m1_subset_1(k1_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_907])).

cnf(c_974,plain,
    ( m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_907])).

cnf(c_19,negated_conjecture,
    ( ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
    | ~ r3_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_428,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_429,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_433,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_23,c_21,c_78])).

cnf(c_434,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | r3_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_463,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k1_yellow_0(sK2,sK3) != X0
    | k1_yellow_0(sK2,sK4) != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_434])).

cnf(c_464,plain,
    ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))
    | ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k1_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1614,c_1564,c_1536,c_1369,c_1368,c_1363,c_1362,c_1359,c_974,c_464])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.39/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.39/1.02  
% 1.39/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.39/1.02  
% 1.39/1.02  ------  iProver source info
% 1.39/1.02  
% 1.39/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.39/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.39/1.02  git: non_committed_changes: false
% 1.39/1.02  git: last_make_outside_of_git: false
% 1.39/1.02  
% 1.39/1.02  ------ 
% 1.39/1.02  
% 1.39/1.02  ------ Input Options
% 1.39/1.02  
% 1.39/1.02  --out_options                           all
% 1.39/1.02  --tptp_safe_out                         true
% 1.39/1.02  --problem_path                          ""
% 1.39/1.02  --include_path                          ""
% 1.39/1.02  --clausifier                            res/vclausify_rel
% 1.39/1.02  --clausifier_options                    --mode clausify
% 1.39/1.02  --stdin                                 false
% 1.39/1.02  --stats_out                             all
% 1.39/1.02  
% 1.39/1.02  ------ General Options
% 1.39/1.02  
% 1.39/1.02  --fof                                   false
% 1.39/1.02  --time_out_real                         305.
% 1.39/1.02  --time_out_virtual                      -1.
% 1.39/1.02  --symbol_type_check                     false
% 1.39/1.02  --clausify_out                          false
% 1.39/1.02  --sig_cnt_out                           false
% 1.39/1.02  --trig_cnt_out                          false
% 1.39/1.02  --trig_cnt_out_tolerance                1.
% 1.39/1.02  --trig_cnt_out_sk_spl                   false
% 1.39/1.02  --abstr_cl_out                          false
% 1.39/1.02  
% 1.39/1.02  ------ Global Options
% 1.39/1.02  
% 1.39/1.02  --schedule                              default
% 1.39/1.02  --add_important_lit                     false
% 1.39/1.02  --prop_solver_per_cl                    1000
% 1.39/1.02  --min_unsat_core                        false
% 1.39/1.02  --soft_assumptions                      false
% 1.39/1.02  --soft_lemma_size                       3
% 1.39/1.02  --prop_impl_unit_size                   0
% 1.39/1.02  --prop_impl_unit                        []
% 1.39/1.02  --share_sel_clauses                     true
% 1.39/1.02  --reset_solvers                         false
% 1.39/1.02  --bc_imp_inh                            [conj_cone]
% 1.39/1.02  --conj_cone_tolerance                   3.
% 1.39/1.02  --extra_neg_conj                        none
% 1.39/1.02  --large_theory_mode                     true
% 1.39/1.02  --prolific_symb_bound                   200
% 1.39/1.02  --lt_threshold                          2000
% 1.39/1.02  --clause_weak_htbl                      true
% 1.39/1.02  --gc_record_bc_elim                     false
% 1.39/1.02  
% 1.39/1.02  ------ Preprocessing Options
% 1.39/1.02  
% 1.39/1.02  --preprocessing_flag                    true
% 1.39/1.02  --time_out_prep_mult                    0.1
% 1.39/1.02  --splitting_mode                        input
% 1.39/1.02  --splitting_grd                         true
% 1.39/1.02  --splitting_cvd                         false
% 1.39/1.02  --splitting_cvd_svl                     false
% 1.39/1.02  --splitting_nvd                         32
% 1.39/1.02  --sub_typing                            true
% 1.39/1.02  --prep_gs_sim                           true
% 1.39/1.02  --prep_unflatten                        true
% 1.39/1.02  --prep_res_sim                          true
% 1.39/1.02  --prep_upred                            true
% 1.39/1.02  --prep_sem_filter                       exhaustive
% 1.39/1.02  --prep_sem_filter_out                   false
% 1.39/1.02  --pred_elim                             true
% 1.39/1.02  --res_sim_input                         true
% 1.39/1.02  --eq_ax_congr_red                       true
% 1.39/1.02  --pure_diseq_elim                       true
% 1.39/1.02  --brand_transform                       false
% 1.39/1.02  --non_eq_to_eq                          false
% 1.39/1.02  --prep_def_merge                        true
% 1.39/1.02  --prep_def_merge_prop_impl              false
% 1.39/1.02  --prep_def_merge_mbd                    true
% 1.39/1.02  --prep_def_merge_tr_red                 false
% 1.39/1.02  --prep_def_merge_tr_cl                  false
% 1.39/1.02  --smt_preprocessing                     true
% 1.39/1.02  --smt_ac_axioms                         fast
% 1.39/1.02  --preprocessed_out                      false
% 1.39/1.02  --preprocessed_stats                    false
% 1.39/1.02  
% 1.39/1.02  ------ Abstraction refinement Options
% 1.39/1.02  
% 1.39/1.02  --abstr_ref                             []
% 1.39/1.02  --abstr_ref_prep                        false
% 1.39/1.02  --abstr_ref_until_sat                   false
% 1.39/1.02  --abstr_ref_sig_restrict                funpre
% 1.39/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.39/1.02  --abstr_ref_under                       []
% 1.39/1.02  
% 1.39/1.02  ------ SAT Options
% 1.39/1.02  
% 1.39/1.02  --sat_mode                              false
% 1.39/1.02  --sat_fm_restart_options                ""
% 1.39/1.02  --sat_gr_def                            false
% 1.39/1.02  --sat_epr_types                         true
% 1.39/1.02  --sat_non_cyclic_types                  false
% 1.39/1.02  --sat_finite_models                     false
% 1.39/1.02  --sat_fm_lemmas                         false
% 1.39/1.02  --sat_fm_prep                           false
% 1.39/1.02  --sat_fm_uc_incr                        true
% 1.39/1.02  --sat_out_model                         small
% 1.39/1.02  --sat_out_clauses                       false
% 1.39/1.02  
% 1.39/1.02  ------ QBF Options
% 1.39/1.02  
% 1.39/1.02  --qbf_mode                              false
% 1.39/1.02  --qbf_elim_univ                         false
% 1.39/1.02  --qbf_dom_inst                          none
% 1.39/1.02  --qbf_dom_pre_inst                      false
% 1.39/1.02  --qbf_sk_in                             false
% 1.39/1.02  --qbf_pred_elim                         true
% 1.39/1.02  --qbf_split                             512
% 1.39/1.02  
% 1.39/1.02  ------ BMC1 Options
% 1.39/1.02  
% 1.39/1.02  --bmc1_incremental                      false
% 1.39/1.02  --bmc1_axioms                           reachable_all
% 1.39/1.02  --bmc1_min_bound                        0
% 1.39/1.02  --bmc1_max_bound                        -1
% 1.39/1.02  --bmc1_max_bound_default                -1
% 1.39/1.02  --bmc1_symbol_reachability              true
% 1.39/1.02  --bmc1_property_lemmas                  false
% 1.39/1.02  --bmc1_k_induction                      false
% 1.39/1.02  --bmc1_non_equiv_states                 false
% 1.39/1.02  --bmc1_deadlock                         false
% 1.39/1.02  --bmc1_ucm                              false
% 1.39/1.02  --bmc1_add_unsat_core                   none
% 1.39/1.02  --bmc1_unsat_core_children              false
% 1.39/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.39/1.02  --bmc1_out_stat                         full
% 1.39/1.02  --bmc1_ground_init                      false
% 1.39/1.02  --bmc1_pre_inst_next_state              false
% 1.39/1.02  --bmc1_pre_inst_state                   false
% 1.39/1.02  --bmc1_pre_inst_reach_state             false
% 1.39/1.02  --bmc1_out_unsat_core                   false
% 1.39/1.02  --bmc1_aig_witness_out                  false
% 1.39/1.02  --bmc1_verbose                          false
% 1.39/1.02  --bmc1_dump_clauses_tptp                false
% 1.39/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.39/1.02  --bmc1_dump_file                        -
% 1.39/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.39/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.39/1.02  --bmc1_ucm_extend_mode                  1
% 1.39/1.02  --bmc1_ucm_init_mode                    2
% 1.39/1.02  --bmc1_ucm_cone_mode                    none
% 1.39/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.39/1.02  --bmc1_ucm_relax_model                  4
% 1.39/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.39/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.39/1.02  --bmc1_ucm_layered_model                none
% 1.39/1.02  --bmc1_ucm_max_lemma_size               10
% 1.39/1.02  
% 1.39/1.02  ------ AIG Options
% 1.39/1.02  
% 1.39/1.02  --aig_mode                              false
% 1.39/1.02  
% 1.39/1.02  ------ Instantiation Options
% 1.39/1.02  
% 1.39/1.02  --instantiation_flag                    true
% 1.39/1.02  --inst_sos_flag                         false
% 1.39/1.02  --inst_sos_phase                        true
% 1.39/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.39/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.39/1.02  --inst_lit_sel_side                     num_symb
% 1.39/1.02  --inst_solver_per_active                1400
% 1.39/1.02  --inst_solver_calls_frac                1.
% 1.39/1.02  --inst_passive_queue_type               priority_queues
% 1.39/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.39/1.02  --inst_passive_queues_freq              [25;2]
% 1.39/1.02  --inst_dismatching                      true
% 1.39/1.02  --inst_eager_unprocessed_to_passive     true
% 1.39/1.02  --inst_prop_sim_given                   true
% 1.39/1.02  --inst_prop_sim_new                     false
% 1.39/1.02  --inst_subs_new                         false
% 1.39/1.02  --inst_eq_res_simp                      false
% 1.39/1.02  --inst_subs_given                       false
% 1.39/1.02  --inst_orphan_elimination               true
% 1.39/1.02  --inst_learning_loop_flag               true
% 1.39/1.02  --inst_learning_start                   3000
% 1.39/1.02  --inst_learning_factor                  2
% 1.39/1.02  --inst_start_prop_sim_after_learn       3
% 1.39/1.02  --inst_sel_renew                        solver
% 1.39/1.02  --inst_lit_activity_flag                true
% 1.39/1.02  --inst_restr_to_given                   false
% 1.39/1.02  --inst_activity_threshold               500
% 1.39/1.02  --inst_out_proof                        true
% 1.39/1.02  
% 1.39/1.02  ------ Resolution Options
% 1.39/1.02  
% 1.39/1.02  --resolution_flag                       true
% 1.39/1.02  --res_lit_sel                           adaptive
% 1.39/1.02  --res_lit_sel_side                      none
% 1.39/1.02  --res_ordering                          kbo
% 1.39/1.02  --res_to_prop_solver                    active
% 1.39/1.02  --res_prop_simpl_new                    false
% 1.39/1.02  --res_prop_simpl_given                  true
% 1.39/1.02  --res_passive_queue_type                priority_queues
% 1.39/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.39/1.02  --res_passive_queues_freq               [15;5]
% 1.39/1.02  --res_forward_subs                      full
% 1.39/1.02  --res_backward_subs                     full
% 1.39/1.02  --res_forward_subs_resolution           true
% 1.39/1.02  --res_backward_subs_resolution          true
% 1.39/1.02  --res_orphan_elimination                true
% 1.39/1.02  --res_time_limit                        2.
% 1.39/1.02  --res_out_proof                         true
% 1.39/1.02  
% 1.39/1.02  ------ Superposition Options
% 1.39/1.02  
% 1.39/1.02  --superposition_flag                    true
% 1.39/1.02  --sup_passive_queue_type                priority_queues
% 1.39/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.39/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.39/1.02  --demod_completeness_check              fast
% 1.39/1.02  --demod_use_ground                      true
% 1.39/1.02  --sup_to_prop_solver                    passive
% 1.39/1.02  --sup_prop_simpl_new                    true
% 1.39/1.02  --sup_prop_simpl_given                  true
% 1.39/1.02  --sup_fun_splitting                     false
% 1.39/1.02  --sup_smt_interval                      50000
% 1.39/1.02  
% 1.39/1.02  ------ Superposition Simplification Setup
% 1.39/1.02  
% 1.39/1.02  --sup_indices_passive                   []
% 1.39/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.39/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.02  --sup_full_bw                           [BwDemod]
% 1.39/1.02  --sup_immed_triv                        [TrivRules]
% 1.39/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.39/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.02  --sup_immed_bw_main                     []
% 1.39/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.39/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.02  
% 1.39/1.02  ------ Combination Options
% 1.39/1.02  
% 1.39/1.02  --comb_res_mult                         3
% 1.39/1.02  --comb_sup_mult                         2
% 1.39/1.02  --comb_inst_mult                        10
% 1.39/1.02  
% 1.39/1.02  ------ Debug Options
% 1.39/1.02  
% 1.39/1.02  --dbg_backtrace                         false
% 1.39/1.02  --dbg_dump_prop_clauses                 false
% 1.39/1.02  --dbg_dump_prop_clauses_file            -
% 1.39/1.02  --dbg_out_stat                          false
% 1.39/1.02  ------ Parsing...
% 1.39/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.39/1.02  
% 1.39/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.39/1.02  
% 1.39/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.39/1.02  
% 1.39/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.39/1.02  ------ Proving...
% 1.39/1.02  ------ Problem Properties 
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  clauses                                 15
% 1.39/1.02  conjectures                             0
% 1.39/1.02  EPR                                     0
% 1.39/1.02  Horn                                    11
% 1.39/1.02  unary                                   4
% 1.39/1.02  binary                                  0
% 1.39/1.02  lits                                    43
% 1.39/1.02  lits eq                                 6
% 1.39/1.02  fd_pure                                 0
% 1.39/1.02  fd_pseudo                               0
% 1.39/1.02  fd_cond                                 0
% 1.39/1.02  fd_pseudo_cond                          6
% 1.39/1.02  AC symbols                              0
% 1.39/1.02  
% 1.39/1.02  ------ Schedule dynamic 5 is on 
% 1.39/1.02  
% 1.39/1.02  ------ no conjectures: strip conj schedule 
% 1.39/1.02  
% 1.39/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  ------ 
% 1.39/1.02  Current options:
% 1.39/1.02  ------ 
% 1.39/1.02  
% 1.39/1.02  ------ Input Options
% 1.39/1.02  
% 1.39/1.02  --out_options                           all
% 1.39/1.02  --tptp_safe_out                         true
% 1.39/1.02  --problem_path                          ""
% 1.39/1.02  --include_path                          ""
% 1.39/1.02  --clausifier                            res/vclausify_rel
% 1.39/1.02  --clausifier_options                    --mode clausify
% 1.39/1.02  --stdin                                 false
% 1.39/1.02  --stats_out                             all
% 1.39/1.02  
% 1.39/1.02  ------ General Options
% 1.39/1.02  
% 1.39/1.02  --fof                                   false
% 1.39/1.02  --time_out_real                         305.
% 1.39/1.02  --time_out_virtual                      -1.
% 1.39/1.02  --symbol_type_check                     false
% 1.39/1.02  --clausify_out                          false
% 1.39/1.02  --sig_cnt_out                           false
% 1.39/1.02  --trig_cnt_out                          false
% 1.39/1.02  --trig_cnt_out_tolerance                1.
% 1.39/1.02  --trig_cnt_out_sk_spl                   false
% 1.39/1.02  --abstr_cl_out                          false
% 1.39/1.02  
% 1.39/1.02  ------ Global Options
% 1.39/1.02  
% 1.39/1.02  --schedule                              default
% 1.39/1.02  --add_important_lit                     false
% 1.39/1.02  --prop_solver_per_cl                    1000
% 1.39/1.02  --min_unsat_core                        false
% 1.39/1.02  --soft_assumptions                      false
% 1.39/1.02  --soft_lemma_size                       3
% 1.39/1.02  --prop_impl_unit_size                   0
% 1.39/1.02  --prop_impl_unit                        []
% 1.39/1.02  --share_sel_clauses                     true
% 1.39/1.02  --reset_solvers                         false
% 1.39/1.02  --bc_imp_inh                            [conj_cone]
% 1.39/1.02  --conj_cone_tolerance                   3.
% 1.39/1.02  --extra_neg_conj                        none
% 1.39/1.02  --large_theory_mode                     true
% 1.39/1.02  --prolific_symb_bound                   200
% 1.39/1.02  --lt_threshold                          2000
% 1.39/1.02  --clause_weak_htbl                      true
% 1.39/1.02  --gc_record_bc_elim                     false
% 1.39/1.02  
% 1.39/1.02  ------ Preprocessing Options
% 1.39/1.02  
% 1.39/1.02  --preprocessing_flag                    true
% 1.39/1.02  --time_out_prep_mult                    0.1
% 1.39/1.02  --splitting_mode                        input
% 1.39/1.02  --splitting_grd                         true
% 1.39/1.02  --splitting_cvd                         false
% 1.39/1.02  --splitting_cvd_svl                     false
% 1.39/1.02  --splitting_nvd                         32
% 1.39/1.02  --sub_typing                            true
% 1.39/1.02  --prep_gs_sim                           true
% 1.39/1.02  --prep_unflatten                        true
% 1.39/1.02  --prep_res_sim                          true
% 1.39/1.02  --prep_upred                            true
% 1.39/1.02  --prep_sem_filter                       exhaustive
% 1.39/1.02  --prep_sem_filter_out                   false
% 1.39/1.02  --pred_elim                             true
% 1.39/1.02  --res_sim_input                         true
% 1.39/1.02  --eq_ax_congr_red                       true
% 1.39/1.02  --pure_diseq_elim                       true
% 1.39/1.02  --brand_transform                       false
% 1.39/1.02  --non_eq_to_eq                          false
% 1.39/1.02  --prep_def_merge                        true
% 1.39/1.02  --prep_def_merge_prop_impl              false
% 1.39/1.02  --prep_def_merge_mbd                    true
% 1.39/1.02  --prep_def_merge_tr_red                 false
% 1.39/1.02  --prep_def_merge_tr_cl                  false
% 1.39/1.02  --smt_preprocessing                     true
% 1.39/1.02  --smt_ac_axioms                         fast
% 1.39/1.02  --preprocessed_out                      false
% 1.39/1.02  --preprocessed_stats                    false
% 1.39/1.02  
% 1.39/1.02  ------ Abstraction refinement Options
% 1.39/1.02  
% 1.39/1.02  --abstr_ref                             []
% 1.39/1.02  --abstr_ref_prep                        false
% 1.39/1.02  --abstr_ref_until_sat                   false
% 1.39/1.02  --abstr_ref_sig_restrict                funpre
% 1.39/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.39/1.02  --abstr_ref_under                       []
% 1.39/1.02  
% 1.39/1.02  ------ SAT Options
% 1.39/1.02  
% 1.39/1.02  --sat_mode                              false
% 1.39/1.02  --sat_fm_restart_options                ""
% 1.39/1.02  --sat_gr_def                            false
% 1.39/1.02  --sat_epr_types                         true
% 1.39/1.02  --sat_non_cyclic_types                  false
% 1.39/1.02  --sat_finite_models                     false
% 1.39/1.02  --sat_fm_lemmas                         false
% 1.39/1.02  --sat_fm_prep                           false
% 1.39/1.02  --sat_fm_uc_incr                        true
% 1.39/1.02  --sat_out_model                         small
% 1.39/1.02  --sat_out_clauses                       false
% 1.39/1.02  
% 1.39/1.02  ------ QBF Options
% 1.39/1.02  
% 1.39/1.02  --qbf_mode                              false
% 1.39/1.02  --qbf_elim_univ                         false
% 1.39/1.02  --qbf_dom_inst                          none
% 1.39/1.02  --qbf_dom_pre_inst                      false
% 1.39/1.02  --qbf_sk_in                             false
% 1.39/1.02  --qbf_pred_elim                         true
% 1.39/1.02  --qbf_split                             512
% 1.39/1.02  
% 1.39/1.02  ------ BMC1 Options
% 1.39/1.02  
% 1.39/1.02  --bmc1_incremental                      false
% 1.39/1.02  --bmc1_axioms                           reachable_all
% 1.39/1.02  --bmc1_min_bound                        0
% 1.39/1.02  --bmc1_max_bound                        -1
% 1.39/1.02  --bmc1_max_bound_default                -1
% 1.39/1.02  --bmc1_symbol_reachability              true
% 1.39/1.02  --bmc1_property_lemmas                  false
% 1.39/1.02  --bmc1_k_induction                      false
% 1.39/1.02  --bmc1_non_equiv_states                 false
% 1.39/1.02  --bmc1_deadlock                         false
% 1.39/1.02  --bmc1_ucm                              false
% 1.39/1.02  --bmc1_add_unsat_core                   none
% 1.39/1.02  --bmc1_unsat_core_children              false
% 1.39/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.39/1.02  --bmc1_out_stat                         full
% 1.39/1.02  --bmc1_ground_init                      false
% 1.39/1.02  --bmc1_pre_inst_next_state              false
% 1.39/1.02  --bmc1_pre_inst_state                   false
% 1.39/1.02  --bmc1_pre_inst_reach_state             false
% 1.39/1.02  --bmc1_out_unsat_core                   false
% 1.39/1.02  --bmc1_aig_witness_out                  false
% 1.39/1.02  --bmc1_verbose                          false
% 1.39/1.02  --bmc1_dump_clauses_tptp                false
% 1.39/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.39/1.02  --bmc1_dump_file                        -
% 1.39/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.39/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.39/1.02  --bmc1_ucm_extend_mode                  1
% 1.39/1.02  --bmc1_ucm_init_mode                    2
% 1.39/1.02  --bmc1_ucm_cone_mode                    none
% 1.39/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.39/1.02  --bmc1_ucm_relax_model                  4
% 1.39/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.39/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.39/1.02  --bmc1_ucm_layered_model                none
% 1.39/1.02  --bmc1_ucm_max_lemma_size               10
% 1.39/1.02  
% 1.39/1.02  ------ AIG Options
% 1.39/1.02  
% 1.39/1.02  --aig_mode                              false
% 1.39/1.02  
% 1.39/1.02  ------ Instantiation Options
% 1.39/1.02  
% 1.39/1.02  --instantiation_flag                    true
% 1.39/1.02  --inst_sos_flag                         false
% 1.39/1.02  --inst_sos_phase                        true
% 1.39/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.39/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.39/1.02  --inst_lit_sel_side                     none
% 1.39/1.02  --inst_solver_per_active                1400
% 1.39/1.02  --inst_solver_calls_frac                1.
% 1.39/1.02  --inst_passive_queue_type               priority_queues
% 1.39/1.02  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.39/1.02  --inst_passive_queues_freq              [25;2]
% 1.39/1.02  --inst_dismatching                      true
% 1.39/1.02  --inst_eager_unprocessed_to_passive     true
% 1.39/1.02  --inst_prop_sim_given                   true
% 1.39/1.02  --inst_prop_sim_new                     false
% 1.39/1.02  --inst_subs_new                         false
% 1.39/1.02  --inst_eq_res_simp                      false
% 1.39/1.02  --inst_subs_given                       false
% 1.39/1.02  --inst_orphan_elimination               true
% 1.39/1.02  --inst_learning_loop_flag               true
% 1.39/1.02  --inst_learning_start                   3000
% 1.39/1.02  --inst_learning_factor                  2
% 1.39/1.02  --inst_start_prop_sim_after_learn       3
% 1.39/1.02  --inst_sel_renew                        solver
% 1.39/1.02  --inst_lit_activity_flag                true
% 1.39/1.02  --inst_restr_to_given                   false
% 1.39/1.02  --inst_activity_threshold               500
% 1.39/1.02  --inst_out_proof                        true
% 1.39/1.02  
% 1.39/1.02  ------ Resolution Options
% 1.39/1.02  
% 1.39/1.02  --resolution_flag                       false
% 1.39/1.02  --res_lit_sel                           adaptive
% 1.39/1.02  --res_lit_sel_side                      none
% 1.39/1.02  --res_ordering                          kbo
% 1.39/1.02  --res_to_prop_solver                    active
% 1.39/1.02  --res_prop_simpl_new                    false
% 1.39/1.02  --res_prop_simpl_given                  true
% 1.39/1.02  --res_passive_queue_type                priority_queues
% 1.39/1.02  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.39/1.02  --res_passive_queues_freq               [15;5]
% 1.39/1.02  --res_forward_subs                      full
% 1.39/1.02  --res_backward_subs                     full
% 1.39/1.02  --res_forward_subs_resolution           true
% 1.39/1.02  --res_backward_subs_resolution          true
% 1.39/1.02  --res_orphan_elimination                true
% 1.39/1.02  --res_time_limit                        2.
% 1.39/1.02  --res_out_proof                         true
% 1.39/1.02  
% 1.39/1.02  ------ Superposition Options
% 1.39/1.02  
% 1.39/1.02  --superposition_flag                    true
% 1.39/1.02  --sup_passive_queue_type                priority_queues
% 1.39/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.39/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.39/1.02  --demod_completeness_check              fast
% 1.39/1.02  --demod_use_ground                      true
% 1.39/1.02  --sup_to_prop_solver                    passive
% 1.39/1.02  --sup_prop_simpl_new                    true
% 1.39/1.02  --sup_prop_simpl_given                  true
% 1.39/1.02  --sup_fun_splitting                     false
% 1.39/1.02  --sup_smt_interval                      50000
% 1.39/1.02  
% 1.39/1.02  ------ Superposition Simplification Setup
% 1.39/1.02  
% 1.39/1.02  --sup_indices_passive                   []
% 1.39/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.39/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.02  --sup_full_bw                           [BwDemod]
% 1.39/1.02  --sup_immed_triv                        [TrivRules]
% 1.39/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.39/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.02  --sup_immed_bw_main                     []
% 1.39/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.39/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.02  
% 1.39/1.02  ------ Combination Options
% 1.39/1.02  
% 1.39/1.02  --comb_res_mult                         3
% 1.39/1.02  --comb_sup_mult                         2
% 1.39/1.02  --comb_inst_mult                        10
% 1.39/1.02  
% 1.39/1.02  ------ Debug Options
% 1.39/1.02  
% 1.39/1.02  --dbg_backtrace                         false
% 1.39/1.02  --dbg_dump_prop_clauses                 false
% 1.39/1.02  --dbg_dump_prop_clauses_file            -
% 1.39/1.02  --dbg_out_stat                          false
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  ------ Proving...
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  % SZS status Theorem for theBenchmark.p
% 1.39/1.02  
% 1.39/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.39/1.02  
% 1.39/1.02  fof(f3,axiom,(
% 1.39/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 1.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/1.02  
% 1.39/1.02  fof(f17,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(ennf_transformation,[],[f3])).
% 1.39/1.02  
% 1.39/1.02  fof(f18,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(flattening,[],[f17])).
% 1.39/1.02  
% 1.39/1.02  fof(f29,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(nnf_transformation,[],[f18])).
% 1.39/1.02  
% 1.39/1.02  fof(f30,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(flattening,[],[f29])).
% 1.39/1.02  
% 1.39/1.02  fof(f31,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(rectify,[],[f30])).
% 1.39/1.02  
% 1.39/1.02  fof(f32,plain,(
% 1.39/1.02    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.39/1.02    introduced(choice_axiom,[])).
% 1.39/1.02  
% 1.39/1.02  fof(f33,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK0(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK0(X0,X1,X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 1.39/1.02  
% 1.39/1.02  fof(f46,plain,(
% 1.39/1.02    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f33])).
% 1.39/1.02  
% 1.39/1.02  fof(f68,plain,(
% 1.39/1.02    ( ! [X4,X0,X1] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(equality_resolution,[],[f46])).
% 1.39/1.02  
% 1.39/1.02  fof(f6,axiom,(
% 1.39/1.02    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/1.02  
% 1.39/1.02  fof(f22,plain,(
% 1.39/1.02    ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(ennf_transformation,[],[f6])).
% 1.39/1.02  
% 1.39/1.02  fof(f56,plain,(
% 1.39/1.02    ( ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f22])).
% 1.39/1.02  
% 1.39/1.02  fof(f7,axiom,(
% 1.39/1.02    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)))),
% 1.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/1.02  
% 1.39/1.02  fof(f23,plain,(
% 1.39/1.02    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | (~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/1.02    inference(ennf_transformation,[],[f7])).
% 1.39/1.02  
% 1.39/1.02  fof(f24,plain,(
% 1.39/1.02    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.39/1.02    inference(flattening,[],[f23])).
% 1.39/1.02  
% 1.39/1.02  fof(f58,plain,(
% 1.39/1.02    ( ! [X0,X1] : (r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f24])).
% 1.39/1.02  
% 1.39/1.02  fof(f9,conjecture,(
% 1.39/1.02    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 1.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/1.02  
% 1.39/1.02  fof(f10,negated_conjecture,(
% 1.39/1.02    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 1.39/1.02    inference(negated_conjecture,[],[f9])).
% 1.39/1.02  
% 1.39/1.02  fof(f11,plain,(
% 1.39/1.02    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 1.39/1.02    inference(pure_predicate_removal,[],[f10])).
% 1.39/1.02  
% 1.39/1.02  fof(f12,plain,(
% 1.39/1.02    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 1.39/1.02    inference(pure_predicate_removal,[],[f11])).
% 1.39/1.02  
% 1.39/1.02  fof(f26,plain,(
% 1.39/1.02    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & (l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 1.39/1.02    inference(ennf_transformation,[],[f12])).
% 1.39/1.02  
% 1.39/1.02  fof(f27,plain,(
% 1.39/1.02    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.39/1.02    inference(flattening,[],[f26])).
% 1.39/1.02  
% 1.39/1.02  fof(f40,plain,(
% 1.39/1.02    ( ! [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) => ((~r1_orders_2(X0,k2_yellow_0(X0,sK4),k2_yellow_0(X0,sK3)) | ~r3_orders_2(X0,k1_yellow_0(X0,sK3),k1_yellow_0(X0,sK4))) & r1_tarski(sK3,sK4))) )),
% 1.39/1.02    introduced(choice_axiom,[])).
% 1.39/1.02  
% 1.39/1.02  fof(f39,plain,(
% 1.39/1.02    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X2,X1] : ((~r1_orders_2(sK2,k2_yellow_0(sK2,X2),k2_yellow_0(sK2,X1)) | ~r3_orders_2(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,X2))) & r1_tarski(X1,X2)) & l1_orders_2(sK2) & v3_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2))),
% 1.39/1.02    introduced(choice_axiom,[])).
% 1.39/1.02  
% 1.39/1.02  fof(f41,plain,(
% 1.39/1.02    ((~r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)) | ~r3_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))) & r1_tarski(sK3,sK4)) & l1_orders_2(sK2) & v3_lattice3(sK2) & v1_lattice3(sK2) & v5_orders_2(sK2) & v3_orders_2(sK2)),
% 1.39/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f40,f39])).
% 1.39/1.02  
% 1.39/1.02  fof(f64,plain,(
% 1.39/1.02    v3_lattice3(sK2)),
% 1.39/1.02    inference(cnf_transformation,[],[f41])).
% 1.39/1.02  
% 1.39/1.02  fof(f62,plain,(
% 1.39/1.02    v5_orders_2(sK2)),
% 1.39/1.02    inference(cnf_transformation,[],[f41])).
% 1.39/1.02  
% 1.39/1.02  fof(f63,plain,(
% 1.39/1.02    v1_lattice3(sK2)),
% 1.39/1.02    inference(cnf_transformation,[],[f41])).
% 1.39/1.02  
% 1.39/1.02  fof(f65,plain,(
% 1.39/1.02    l1_orders_2(sK2)),
% 1.39/1.02    inference(cnf_transformation,[],[f41])).
% 1.39/1.02  
% 1.39/1.02  fof(f2,axiom,(
% 1.39/1.02    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/1.02  
% 1.39/1.02  fof(f15,plain,(
% 1.39/1.02    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(ennf_transformation,[],[f2])).
% 1.39/1.02  
% 1.39/1.02  fof(f16,plain,(
% 1.39/1.02    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(flattening,[],[f15])).
% 1.39/1.02  
% 1.39/1.02  fof(f44,plain,(
% 1.39/1.02    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f16])).
% 1.39/1.02  
% 1.39/1.02  fof(f4,axiom,(
% 1.39/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/1.02  
% 1.39/1.02  fof(f19,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(ennf_transformation,[],[f4])).
% 1.39/1.02  
% 1.39/1.02  fof(f20,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(flattening,[],[f19])).
% 1.39/1.02  
% 1.39/1.02  fof(f34,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(nnf_transformation,[],[f20])).
% 1.39/1.02  
% 1.39/1.02  fof(f35,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(flattening,[],[f34])).
% 1.39/1.02  
% 1.39/1.02  fof(f36,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(rectify,[],[f35])).
% 1.39/1.02  
% 1.39/1.02  fof(f37,plain,(
% 1.39/1.02    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.39/1.02    introduced(choice_axiom,[])).
% 1.39/1.02  
% 1.39/1.02  fof(f38,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK1(X0,X1,X2)) & r2_lattice3(X0,X1,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 1.39/1.02  
% 1.39/1.02  fof(f51,plain,(
% 1.39/1.02    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f38])).
% 1.39/1.02  
% 1.39/1.02  fof(f70,plain,(
% 1.39/1.02    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(equality_resolution,[],[f51])).
% 1.39/1.02  
% 1.39/1.02  fof(f5,axiom,(
% 1.39/1.02    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/1.02  
% 1.39/1.02  fof(f21,plain,(
% 1.39/1.02    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(ennf_transformation,[],[f5])).
% 1.39/1.02  
% 1.39/1.02  fof(f55,plain,(
% 1.39/1.02    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f21])).
% 1.39/1.02  
% 1.39/1.02  fof(f57,plain,(
% 1.39/1.02    ( ! [X0,X1] : (r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f24])).
% 1.39/1.02  
% 1.39/1.02  fof(f50,plain,(
% 1.39/1.02    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f38])).
% 1.39/1.02  
% 1.39/1.02  fof(f71,plain,(
% 1.39/1.02    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(equality_resolution,[],[f50])).
% 1.39/1.02  
% 1.39/1.02  fof(f8,axiom,(
% 1.39/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 1.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/1.02  
% 1.39/1.02  fof(f25,plain,(
% 1.39/1.02    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.39/1.02    inference(ennf_transformation,[],[f8])).
% 1.39/1.02  
% 1.39/1.02  fof(f60,plain,(
% 1.39/1.02    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f25])).
% 1.39/1.02  
% 1.39/1.02  fof(f66,plain,(
% 1.39/1.02    r1_tarski(sK3,sK4)),
% 1.39/1.02    inference(cnf_transformation,[],[f41])).
% 1.39/1.02  
% 1.39/1.02  fof(f45,plain,(
% 1.39/1.02    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f33])).
% 1.39/1.02  
% 1.39/1.02  fof(f69,plain,(
% 1.39/1.02    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(equality_resolution,[],[f45])).
% 1.39/1.02  
% 1.39/1.02  fof(f59,plain,(
% 1.39/1.02    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f25])).
% 1.39/1.02  
% 1.39/1.02  fof(f67,plain,(
% 1.39/1.02    ~r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)) | ~r3_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))),
% 1.39/1.02    inference(cnf_transformation,[],[f41])).
% 1.39/1.02  
% 1.39/1.02  fof(f1,axiom,(
% 1.39/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.39/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.39/1.02  
% 1.39/1.02  fof(f13,plain,(
% 1.39/1.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.39/1.02    inference(ennf_transformation,[],[f1])).
% 1.39/1.02  
% 1.39/1.02  fof(f14,plain,(
% 1.39/1.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/1.02    inference(flattening,[],[f13])).
% 1.39/1.02  
% 1.39/1.02  fof(f28,plain,(
% 1.39/1.02    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.39/1.02    inference(nnf_transformation,[],[f14])).
% 1.39/1.02  
% 1.39/1.02  fof(f43,plain,(
% 1.39/1.02    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.39/1.02    inference(cnf_transformation,[],[f28])).
% 1.39/1.02  
% 1.39/1.02  fof(f61,plain,(
% 1.39/1.02    v3_orders_2(sK2)),
% 1.39/1.02    inference(cnf_transformation,[],[f41])).
% 1.39/1.02  
% 1.39/1.02  cnf(c_6,plain,
% 1.39/1.02      ( ~ r1_lattice3(X0,X1,X2)
% 1.39/1.02      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.39/1.02      | ~ r2_yellow_0(X0,X1)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f68]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_14,plain,
% 1.39/1.02      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f56]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_176,plain,
% 1.39/1.02      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ r2_yellow_0(X0,X1)
% 1.39/1.02      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.39/1.02      | ~ r1_lattice3(X0,X1,X2)
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_6,c_14]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_177,plain,
% 1.39/1.02      ( ~ r1_lattice3(X0,X1,X2)
% 1.39/1.02      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.39/1.02      | ~ r2_yellow_0(X0,X1)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(renaming,[status(thm)],[c_176]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_15,plain,
% 1.39/1.02      ( r2_yellow_0(X0,X1)
% 1.39/1.02      | ~ v5_orders_2(X0)
% 1.39/1.02      | ~ v3_lattice3(X0)
% 1.39/1.02      | v2_struct_0(X0)
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f58]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_22,negated_conjecture,
% 1.39/1.02      ( v3_lattice3(sK2) ),
% 1.39/1.02      inference(cnf_transformation,[],[f64]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_339,plain,
% 1.39/1.02      ( r2_yellow_0(X0,X1)
% 1.39/1.02      | ~ v5_orders_2(X0)
% 1.39/1.02      | v2_struct_0(X0)
% 1.39/1.02      | ~ l1_orders_2(X0)
% 1.39/1.02      | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_340,plain,
% 1.39/1.02      ( r2_yellow_0(sK2,X0)
% 1.39/1.02      | ~ v5_orders_2(sK2)
% 1.39/1.02      | v2_struct_0(sK2)
% 1.39/1.02      | ~ l1_orders_2(sK2) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_339]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_24,negated_conjecture,
% 1.39/1.02      ( v5_orders_2(sK2) ),
% 1.39/1.02      inference(cnf_transformation,[],[f62]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_23,negated_conjecture,
% 1.39/1.02      ( v1_lattice3(sK2) ),
% 1.39/1.02      inference(cnf_transformation,[],[f63]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_21,negated_conjecture,
% 1.39/1.02      ( l1_orders_2(sK2) ),
% 1.39/1.02      inference(cnf_transformation,[],[f65]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_2,plain,
% 1.39/1.02      ( ~ v1_lattice3(X0) | ~ v2_struct_0(X0) | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_78,plain,
% 1.39/1.02      ( ~ v1_lattice3(sK2) | ~ v2_struct_0(sK2) | ~ l1_orders_2(sK2) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_344,plain,
% 1.39/1.02      ( r2_yellow_0(sK2,X0) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_340,c_24,c_23,c_21,c_78]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_484,plain,
% 1.39/1.02      ( ~ r1_lattice3(X0,X1,X2)
% 1.39/1.02      | r1_orders_2(X0,X2,k2_yellow_0(X0,X1))
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0)
% 1.39/1.02      | X3 != X1
% 1.39/1.02      | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_177,c_344]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_485,plain,
% 1.39/1.02      ( ~ r1_lattice3(sK2,X0,X1)
% 1.39/1.02      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/1.02      | ~ l1_orders_2(sK2) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_484]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_489,plain,
% 1.39/1.02      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/1.02      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 1.39/1.02      | ~ r1_lattice3(sK2,X0,X1) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_485,c_21]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_490,plain,
% 1.39/1.02      ( ~ r1_lattice3(sK2,X0,X1)
% 1.39/1.02      | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(renaming,[status(thm)],[c_489]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_920,plain,
% 1.39/1.02      ( ~ r1_lattice3(sK2,X0_52,X0_51)
% 1.39/1.02      | r1_orders_2(sK2,X0_51,k2_yellow_0(sK2,X0_52))
% 1.39/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(subtyping,[status(esa)],[c_490]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1389,plain,
% 1.39/1.02      ( ~ r1_lattice3(sK2,X0_52,k2_yellow_0(sK2,X1_52))
% 1.39/1.02      | r1_orders_2(sK2,k2_yellow_0(sK2,X1_52),k2_yellow_0(sK2,X0_52))
% 1.39/1.02      | ~ m1_subset_1(k2_yellow_0(sK2,X1_52),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_920]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1614,plain,
% 1.39/1.02      ( ~ r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
% 1.39/1.02      | r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
% 1.39/1.02      | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_1389]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_11,plain,
% 1.39/1.02      ( ~ r2_lattice3(X0,X1,X2)
% 1.39/1.02      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.39/1.02      | ~ r1_yellow_0(X0,X1)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f70]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_13,plain,
% 1.39/1.02      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_159,plain,
% 1.39/1.02      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ r1_yellow_0(X0,X1)
% 1.39/1.02      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.39/1.02      | ~ r2_lattice3(X0,X1,X2)
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_11,c_13]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_160,plain,
% 1.39/1.02      ( ~ r2_lattice3(X0,X1,X2)
% 1.39/1.02      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.39/1.02      | ~ r1_yellow_0(X0,X1)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(renaming,[status(thm)],[c_159]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_16,plain,
% 1.39/1.02      ( r1_yellow_0(X0,X1)
% 1.39/1.02      | ~ v5_orders_2(X0)
% 1.39/1.02      | ~ v3_lattice3(X0)
% 1.39/1.02      | v2_struct_0(X0)
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f57]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_324,plain,
% 1.39/1.02      ( r1_yellow_0(X0,X1)
% 1.39/1.02      | ~ v5_orders_2(X0)
% 1.39/1.02      | v2_struct_0(X0)
% 1.39/1.02      | ~ l1_orders_2(X0)
% 1.39/1.02      | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_325,plain,
% 1.39/1.02      ( r1_yellow_0(sK2,X0)
% 1.39/1.02      | ~ v5_orders_2(sK2)
% 1.39/1.02      | v2_struct_0(sK2)
% 1.39/1.02      | ~ l1_orders_2(sK2) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_324]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_329,plain,
% 1.39/1.02      ( r1_yellow_0(sK2,X0) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_325,c_24,c_23,c_21,c_78]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_613,plain,
% 1.39/1.02      ( ~ r2_lattice3(X0,X1,X2)
% 1.39/1.02      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0)
% 1.39/1.02      | X3 != X1
% 1.39/1.02      | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_160,c_329]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_614,plain,
% 1.39/1.02      ( ~ r2_lattice3(sK2,X0,X1)
% 1.39/1.02      | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/1.02      | ~ l1_orders_2(sK2) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_613]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_618,plain,
% 1.39/1.02      ( ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/1.02      | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 1.39/1.02      | ~ r2_lattice3(sK2,X0,X1) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_614,c_21]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_619,plain,
% 1.39/1.02      ( ~ r2_lattice3(sK2,X0,X1)
% 1.39/1.02      | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(renaming,[status(thm)],[c_618]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_915,plain,
% 1.39/1.02      ( ~ r2_lattice3(sK2,X0_52,X0_51)
% 1.39/1.02      | r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),X0_51)
% 1.39/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(subtyping,[status(esa)],[c_619]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1374,plain,
% 1.39/1.02      ( ~ r2_lattice3(sK2,X0_52,k1_yellow_0(sK2,X1_52))
% 1.39/1.02      | r1_orders_2(sK2,k1_yellow_0(sK2,X0_52),k1_yellow_0(sK2,X1_52))
% 1.39/1.02      | ~ m1_subset_1(k1_yellow_0(sK2,X1_52),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_915]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1564,plain,
% 1.39/1.02      ( ~ r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK4))
% 1.39/1.02      | r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))
% 1.39/1.02      | ~ m1_subset_1(k1_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_1374]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_772,plain,
% 1.39/1.02      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_773,plain,
% 1.39/1.02      ( m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_772]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_908,plain,
% 1.39/1.02      ( m1_subset_1(k2_yellow_0(sK2,X0_52),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(subtyping,[status(esa)],[c_773]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1536,plain,
% 1.39/1.02      ( m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_908]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_12,plain,
% 1.39/1.02      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.39/1.02      | ~ r1_yellow_0(X0,X1)
% 1.39/1.02      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f71]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_152,plain,
% 1.39/1.02      ( ~ r1_yellow_0(X0,X1)
% 1.39/1.02      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_12,c_13]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_153,plain,
% 1.39/1.02      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.39/1.02      | ~ r1_yellow_0(X0,X1)
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(renaming,[status(thm)],[c_152]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_634,plain,
% 1.39/1.02      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
% 1.39/1.02      | ~ l1_orders_2(X0)
% 1.39/1.02      | X2 != X1
% 1.39/1.02      | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_153,c_329]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_635,plain,
% 1.39/1.02      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0)) | ~ l1_orders_2(sK2) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_634]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_639,plain,
% 1.39/1.02      ( r2_lattice3(sK2,X0,k1_yellow_0(sK2,X0)) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_635,c_21]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_914,plain,
% 1.39/1.02      ( r2_lattice3(sK2,X0_52,k1_yellow_0(sK2,X0_52)) ),
% 1.39/1.02      inference(subtyping,[status(esa)],[c_639]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1369,plain,
% 1.39/1.02      ( r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK4)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_914]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_17,plain,
% 1.39/1.02      ( ~ r2_lattice3(X0,X1,X2)
% 1.39/1.02      | r2_lattice3(X0,X3,X2)
% 1.39/1.02      | ~ r1_tarski(X3,X1)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f60]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_20,negated_conjecture,
% 1.39/1.02      ( r1_tarski(sK3,sK4) ),
% 1.39/1.02      inference(cnf_transformation,[],[f66]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_376,plain,
% 1.39/1.02      ( ~ r2_lattice3(X0,X1,X2)
% 1.39/1.02      | r2_lattice3(X0,X3,X2)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0)
% 1.39/1.02      | sK3 != X3
% 1.39/1.02      | sK4 != X1 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_377,plain,
% 1.39/1.02      ( r2_lattice3(X0,sK3,X1)
% 1.39/1.02      | ~ r2_lattice3(X0,sK4,X1)
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_376]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_742,plain,
% 1.39/1.02      ( r2_lattice3(X0,sK3,X1)
% 1.39/1.02      | ~ r2_lattice3(X0,sK4,X1)
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/1.02      | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_377,c_21]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_743,plain,
% 1.39/1.02      ( r2_lattice3(sK2,sK3,X0)
% 1.39/1.02      | ~ r2_lattice3(sK2,sK4,X0)
% 1.39/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_742]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_910,plain,
% 1.39/1.02      ( r2_lattice3(sK2,sK3,X0_51)
% 1.39/1.02      | ~ r2_lattice3(sK2,sK4,X0_51)
% 1.39/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(subtyping,[status(esa)],[c_743]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1368,plain,
% 1.39/1.02      ( r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK4))
% 1.39/1.02      | ~ r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK4))
% 1.39/1.02      | ~ m1_subset_1(k1_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_910]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_7,plain,
% 1.39/1.02      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.39/1.02      | ~ r2_yellow_0(X0,X1)
% 1.39/1.02      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f69]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_169,plain,
% 1.39/1.02      ( ~ r2_yellow_0(X0,X1)
% 1.39/1.02      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_7,c_14]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_170,plain,
% 1.39/1.02      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.39/1.02      | ~ r2_yellow_0(X0,X1)
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(renaming,[status(thm)],[c_169]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_505,plain,
% 1.39/1.02      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
% 1.39/1.02      | ~ l1_orders_2(X0)
% 1.39/1.02      | X2 != X1
% 1.39/1.02      | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_170,c_344]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_506,plain,
% 1.39/1.02      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) | ~ l1_orders_2(sK2) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_505]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_510,plain,
% 1.39/1.02      ( r1_lattice3(sK2,X0,k2_yellow_0(sK2,X0)) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_506,c_21]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_919,plain,
% 1.39/1.02      ( r1_lattice3(sK2,X0_52,k2_yellow_0(sK2,X0_52)) ),
% 1.39/1.02      inference(subtyping,[status(esa)],[c_510]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1363,plain,
% 1.39/1.02      ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_919]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_18,plain,
% 1.39/1.02      ( ~ r1_lattice3(X0,X1,X2)
% 1.39/1.02      | r1_lattice3(X0,X3,X2)
% 1.39/1.02      | ~ r1_tarski(X3,X1)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f59]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_358,plain,
% 1.39/1.02      ( ~ r1_lattice3(X0,X1,X2)
% 1.39/1.02      | r1_lattice3(X0,X3,X2)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0)
% 1.39/1.02      | sK3 != X3
% 1.39/1.02      | sK4 != X1 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_359,plain,
% 1.39/1.02      ( r1_lattice3(X0,sK3,X1)
% 1.39/1.02      | ~ r1_lattice3(X0,sK4,X1)
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_358]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_757,plain,
% 1.39/1.02      ( r1_lattice3(X0,sK3,X1)
% 1.39/1.02      | ~ r1_lattice3(X0,sK4,X1)
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/1.02      | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_359,c_21]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_758,plain,
% 1.39/1.02      ( r1_lattice3(sK2,sK3,X0)
% 1.39/1.02      | ~ r1_lattice3(sK2,sK4,X0)
% 1.39/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_757]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_909,plain,
% 1.39/1.02      ( r1_lattice3(sK2,sK3,X0_51)
% 1.39/1.02      | ~ r1_lattice3(sK2,sK4,X0_51)
% 1.39/1.02      | ~ m1_subset_1(X0_51,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(subtyping,[status(esa)],[c_758]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1362,plain,
% 1.39/1.02      ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK4))
% 1.39/1.02      | ~ r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4))
% 1.39/1.02      | ~ m1_subset_1(k2_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_909]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_781,plain,
% 1.39/1.02      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_782,plain,
% 1.39/1.02      ( m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_781]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_907,plain,
% 1.39/1.02      ( m1_subset_1(k1_yellow_0(sK2,X0_52),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(subtyping,[status(esa)],[c_782]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_1359,plain,
% 1.39/1.02      ( m1_subset_1(k1_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_907]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_974,plain,
% 1.39/1.02      ( m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(instantiation,[status(thm)],[c_907]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_19,negated_conjecture,
% 1.39/1.02      ( ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
% 1.39/1.02      | ~ r3_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4)) ),
% 1.39/1.02      inference(cnf_transformation,[],[f67]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_0,plain,
% 1.39/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 1.39/1.02      | r3_orders_2(X0,X1,X2)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/1.02      | v2_struct_0(X0)
% 1.39/1.02      | ~ v3_orders_2(X0)
% 1.39/1.02      | ~ l1_orders_2(X0) ),
% 1.39/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_25,negated_conjecture,
% 1.39/1.02      ( v3_orders_2(sK2) ),
% 1.39/1.02      inference(cnf_transformation,[],[f61]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_428,plain,
% 1.39/1.02      ( ~ r1_orders_2(X0,X1,X2)
% 1.39/1.02      | r3_orders_2(X0,X1,X2)
% 1.39/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.39/1.02      | v2_struct_0(X0)
% 1.39/1.02      | ~ l1_orders_2(X0)
% 1.39/1.02      | sK2 != X0 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_25]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_429,plain,
% 1.39/1.02      ( ~ r1_orders_2(sK2,X0,X1)
% 1.39/1.02      | r3_orders_2(sK2,X0,X1)
% 1.39/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/1.02      | v2_struct_0(sK2)
% 1.39/1.02      | ~ l1_orders_2(sK2) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_428]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_433,plain,
% 1.39/1.02      ( ~ r1_orders_2(sK2,X0,X1)
% 1.39/1.02      | r3_orders_2(sK2,X0,X1)
% 1.39/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(global_propositional_subsumption,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_429,c_23,c_21,c_78]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_434,plain,
% 1.39/1.02      ( ~ r1_orders_2(sK2,X0,X1)
% 1.39/1.02      | r3_orders_2(sK2,X0,X1)
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 1.39/1.02      inference(renaming,[status(thm)],[c_433]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_463,plain,
% 1.39/1.02      ( ~ r1_orders_2(sK2,X0,X1)
% 1.39/1.02      | ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
% 1.39/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.39/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.39/1.02      | k1_yellow_0(sK2,sK3) != X0
% 1.39/1.02      | k1_yellow_0(sK2,sK4) != X1
% 1.39/1.02      | sK2 != sK2 ),
% 1.39/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_434]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(c_464,plain,
% 1.39/1.02      ( ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))
% 1.39/1.02      | ~ r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
% 1.39/1.02      | ~ m1_subset_1(k1_yellow_0(sK2,sK3),u1_struct_0(sK2))
% 1.39/1.02      | ~ m1_subset_1(k1_yellow_0(sK2,sK4),u1_struct_0(sK2)) ),
% 1.39/1.02      inference(unflattening,[status(thm)],[c_463]) ).
% 1.39/1.02  
% 1.39/1.02  cnf(contradiction,plain,
% 1.39/1.02      ( $false ),
% 1.39/1.02      inference(minisat,
% 1.39/1.02                [status(thm)],
% 1.39/1.02                [c_1614,c_1564,c_1536,c_1369,c_1368,c_1363,c_1362,c_1359,
% 1.39/1.02                 c_974,c_464]) ).
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.39/1.02  
% 1.39/1.02  ------                               Statistics
% 1.39/1.02  
% 1.39/1.02  ------ General
% 1.39/1.02  
% 1.39/1.02  abstr_ref_over_cycles:                  0
% 1.39/1.02  abstr_ref_under_cycles:                 0
% 1.39/1.02  gc_basic_clause_elim:                   0
% 1.39/1.02  forced_gc_time:                         0
% 1.39/1.02  parsing_time:                           0.009
% 1.39/1.02  unif_index_cands_time:                  0.
% 1.39/1.02  unif_index_add_time:                    0.
% 1.39/1.02  orderings_time:                         0.
% 1.39/1.02  out_proof_time:                         0.013
% 1.39/1.02  total_time:                             0.084
% 1.39/1.02  num_of_symbols:                         54
% 1.39/1.02  num_of_terms:                           1316
% 1.39/1.02  
% 1.39/1.02  ------ Preprocessing
% 1.39/1.02  
% 1.39/1.02  num_of_splits:                          0
% 1.39/1.02  num_of_split_atoms:                     0
% 1.39/1.02  num_of_reused_defs:                     0
% 1.39/1.02  num_eq_ax_congr_red:                    37
% 1.39/1.02  num_of_sem_filtered_clauses:            1
% 1.39/1.02  num_of_subtypes:                        4
% 1.39/1.02  monotx_restored_types:                  0
% 1.39/1.02  sat_num_of_epr_types:                   0
% 1.39/1.02  sat_num_of_non_cyclic_types:            0
% 1.39/1.02  sat_guarded_non_collapsed_types:        1
% 1.39/1.02  num_pure_diseq_elim:                    0
% 1.39/1.02  simp_replaced_by:                       0
% 1.39/1.02  res_preprocessed:                       84
% 1.39/1.02  prep_upred:                             0
% 1.39/1.02  prep_unflattend:                        35
% 1.39/1.02  smt_new_axioms:                         0
% 1.39/1.02  pred_elim_cands:                        4
% 1.39/1.02  pred_elim:                              10
% 1.39/1.02  pred_elim_cl:                           11
% 1.39/1.02  pred_elim_cycles:                       12
% 1.39/1.02  merged_defs:                            0
% 1.39/1.02  merged_defs_ncl:                        0
% 1.39/1.02  bin_hyper_res:                          0
% 1.39/1.02  prep_cycles:                            4
% 1.39/1.02  pred_elim_time:                         0.01
% 1.39/1.02  splitting_time:                         0.
% 1.39/1.02  sem_filter_time:                        0.
% 1.39/1.02  monotx_time:                            0.
% 1.39/1.02  subtype_inf_time:                       0.
% 1.39/1.02  
% 1.39/1.02  ------ Problem properties
% 1.39/1.02  
% 1.39/1.02  clauses:                                15
% 1.39/1.02  conjectures:                            0
% 1.39/1.02  epr:                                    0
% 1.39/1.02  horn:                                   11
% 1.39/1.02  ground:                                 1
% 1.39/1.02  unary:                                  4
% 1.39/1.02  binary:                                 0
% 1.39/1.02  lits:                                   43
% 1.39/1.02  lits_eq:                                6
% 1.39/1.02  fd_pure:                                0
% 1.39/1.02  fd_pseudo:                              0
% 1.39/1.02  fd_cond:                                0
% 1.39/1.02  fd_pseudo_cond:                         6
% 1.39/1.02  ac_symbols:                             0
% 1.39/1.02  
% 1.39/1.02  ------ Propositional Solver
% 1.39/1.02  
% 1.39/1.02  prop_solver_calls:                      24
% 1.39/1.02  prop_fast_solver_calls:                 691
% 1.39/1.02  smt_solver_calls:                       0
% 1.39/1.02  smt_fast_solver_calls:                  0
% 1.39/1.02  prop_num_of_clauses:                    447
% 1.39/1.02  prop_preprocess_simplified:             2649
% 1.39/1.02  prop_fo_subsumed:                       25
% 1.39/1.02  prop_solver_time:                       0.
% 1.39/1.02  smt_solver_time:                        0.
% 1.39/1.02  smt_fast_solver_time:                   0.
% 1.39/1.02  prop_fast_solver_time:                  0.
% 1.39/1.02  prop_unsat_core_time:                   0.
% 1.39/1.02  
% 1.39/1.02  ------ QBF
% 1.39/1.02  
% 1.39/1.02  qbf_q_res:                              0
% 1.39/1.02  qbf_num_tautologies:                    0
% 1.39/1.02  qbf_prep_cycles:                        0
% 1.39/1.02  
% 1.39/1.02  ------ BMC1
% 1.39/1.02  
% 1.39/1.02  bmc1_current_bound:                     -1
% 1.39/1.02  bmc1_last_solved_bound:                 -1
% 1.39/1.02  bmc1_unsat_core_size:                   -1
% 1.39/1.02  bmc1_unsat_core_parents_size:           -1
% 1.39/1.02  bmc1_merge_next_fun:                    0
% 1.39/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.39/1.02  
% 1.39/1.02  ------ Instantiation
% 1.39/1.02  
% 1.39/1.02  inst_num_of_clauses:                    56
% 1.39/1.02  inst_num_in_passive:                    9
% 1.39/1.02  inst_num_in_active:                     45
% 1.39/1.02  inst_num_in_unprocessed:                1
% 1.39/1.02  inst_num_of_loops:                      50
% 1.39/1.02  inst_num_of_learning_restarts:          0
% 1.39/1.02  inst_num_moves_active_passive:          3
% 1.39/1.02  inst_lit_activity:                      0
% 1.39/1.02  inst_lit_activity_moves:                0
% 1.39/1.02  inst_num_tautologies:                   0
% 1.39/1.02  inst_num_prop_implied:                  0
% 1.39/1.02  inst_num_existing_simplified:           0
% 1.39/1.02  inst_num_eq_res_simplified:             0
% 1.39/1.02  inst_num_child_elim:                    0
% 1.39/1.02  inst_num_of_dismatching_blockings:      21
% 1.39/1.02  inst_num_of_non_proper_insts:           43
% 1.39/1.02  inst_num_of_duplicates:                 0
% 1.39/1.02  inst_inst_num_from_inst_to_res:         0
% 1.39/1.02  inst_dismatching_checking_time:         0.
% 1.39/1.02  
% 1.39/1.02  ------ Resolution
% 1.39/1.02  
% 1.39/1.02  res_num_of_clauses:                     0
% 1.39/1.02  res_num_in_passive:                     0
% 1.39/1.02  res_num_in_active:                      0
% 1.39/1.02  res_num_of_loops:                       88
% 1.39/1.02  res_forward_subset_subsumed:            2
% 1.39/1.02  res_backward_subset_subsumed:           0
% 1.39/1.02  res_forward_subsumed:                   0
% 1.39/1.02  res_backward_subsumed:                  0
% 1.39/1.02  res_forward_subsumption_resolution:     0
% 1.39/1.02  res_backward_subsumption_resolution:    1
% 1.39/1.02  res_clause_to_clause_subsumption:       43
% 1.39/1.02  res_orphan_elimination:                 0
% 1.39/1.02  res_tautology_del:                      1
% 1.39/1.02  res_num_eq_res_simplified:              0
% 1.39/1.02  res_num_sel_changes:                    0
% 1.39/1.02  res_moves_from_active_to_pass:          0
% 1.39/1.02  
% 1.39/1.02  ------ Superposition
% 1.39/1.02  
% 1.39/1.02  sup_time_total:                         0.
% 1.39/1.02  sup_time_generating:                    0.
% 1.39/1.02  sup_time_sim_full:                      0.
% 1.39/1.02  sup_time_sim_immed:                     0.
% 1.39/1.02  
% 1.39/1.02  sup_num_of_clauses:                     20
% 1.39/1.02  sup_num_in_active:                      8
% 1.39/1.02  sup_num_in_passive:                     12
% 1.39/1.02  sup_num_of_loops:                       8
% 1.39/1.02  sup_fw_superposition:                   5
% 1.39/1.02  sup_bw_superposition:                   0
% 1.39/1.02  sup_immediate_simplified:               0
% 1.39/1.02  sup_given_eliminated:                   0
% 1.39/1.02  comparisons_done:                       0
% 1.39/1.02  comparisons_avoided:                    0
% 1.39/1.02  
% 1.39/1.02  ------ Simplifications
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  sim_fw_subset_subsumed:                 0
% 1.39/1.02  sim_bw_subset_subsumed:                 0
% 1.39/1.02  sim_fw_subsumed:                        0
% 1.39/1.02  sim_bw_subsumed:                        0
% 1.39/1.02  sim_fw_subsumption_res:                 1
% 1.39/1.02  sim_bw_subsumption_res:                 0
% 1.39/1.02  sim_tautology_del:                      0
% 1.39/1.02  sim_eq_tautology_del:                   0
% 1.39/1.02  sim_eq_res_simp:                        0
% 1.39/1.02  sim_fw_demodulated:                     0
% 1.39/1.02  sim_bw_demodulated:                     0
% 1.39/1.02  sim_light_normalised:                   0
% 1.39/1.02  sim_joinable_taut:                      0
% 1.39/1.02  sim_joinable_simp:                      0
% 1.39/1.02  sim_ac_normalised:                      0
% 1.39/1.02  sim_smt_subsumption:                    0
% 1.39/1.02  
%------------------------------------------------------------------------------
