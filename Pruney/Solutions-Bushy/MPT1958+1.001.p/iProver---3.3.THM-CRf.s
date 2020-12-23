%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1958+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:55 EST 2020

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  149 (1232 expanded)
%              Number of clauses        :   98 ( 374 expanded)
%              Number of leaves         :   12 ( 224 expanded)
%              Depth                    :   24
%              Number of atoms          :  506 (6379 expanded)
%              Number of equality atoms :  142 (1474 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v7_struct_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( X1 = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK1(X0) != X1
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK0(X0) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ( sK0(X0) != sK1(X0)
            & m1_subset_1(sK1(X0),u1_struct_0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f38,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> k3_yellow_0(X0) = k4_yellow_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_struct_0(X0)
        <=> k3_yellow_0(X0) = k4_yellow_0(X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f23,plain,(
    ? [X0] :
      ( ( v7_struct_0(X0)
      <~> k3_yellow_0(X0) = k4_yellow_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ( v7_struct_0(X0)
      <~> k3_yellow_0(X0) = k4_yellow_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ? [X0] :
      ( ( k3_yellow_0(X0) != k4_yellow_0(X0)
        | ~ v7_struct_0(X0) )
      & ( k3_yellow_0(X0) = k4_yellow_0(X0)
        | v7_struct_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f31,plain,(
    ? [X0] :
      ( ( k3_yellow_0(X0) != k4_yellow_0(X0)
        | ~ v7_struct_0(X0) )
      & ( k3_yellow_0(X0) = k4_yellow_0(X0)
        | v7_struct_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0] :
        ( ( k3_yellow_0(X0) != k4_yellow_0(X0)
          | ~ v7_struct_0(X0) )
        & ( k3_yellow_0(X0) = k4_yellow_0(X0)
          | v7_struct_0(X0) )
        & l1_orders_2(X0)
        & v3_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k3_yellow_0(sK2) != k4_yellow_0(sK2)
        | ~ v7_struct_0(sK2) )
      & ( k3_yellow_0(sK2) = k4_yellow_0(sK2)
        | v7_struct_0(sK2) )
      & l1_orders_2(sK2)
      & v3_yellow_0(sK2)
      & v5_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k3_yellow_0(sK2) != k4_yellow_0(sK2)
      | ~ v7_struct_0(sK2) )
    & ( k3_yellow_0(sK2) = k4_yellow_0(sK2)
      | v7_struct_0(sK2) )
    & l1_orders_2(sK2)
    & v3_yellow_0(sK2)
    & v5_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f49,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,
    ( k3_yellow_0(sK2) != k4_yellow_0(sK2)
    | ~ v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f36,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    v3_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,
    ( k3_yellow_0(sK2) = k4_yellow_0(sK2)
    | v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | m1_subset_1(sK0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | sK0(X0) != sK1(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( m1_subset_1(sK1(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_14,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_346,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_347,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_383,plain,
    ( m1_subset_1(sK1(X0),u1_struct_0(X0))
    | v7_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_347])).

cnf(c_384,plain,
    ( m1_subset_1(sK1(sK2),u1_struct_0(sK2))
    | v7_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_768,plain,
    ( m1_subset_1(sK1(sK2),u1_struct_0(sK2))
    | v7_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_384])).

cnf(c_1061,plain,
    ( m1_subset_1(sK1(sK2),u1_struct_0(sK2)) = iProver_top
    | v7_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_21,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_33,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_35,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_7,plain,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_36,plain,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_38,plain,
    ( m1_subset_1(k4_yellow_0(sK2),u1_struct_0(sK2)) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_6,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_39,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_41,plain,
    ( m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) = iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_48,plain,
    ( m1_subset_1(sK1(X0),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v7_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_50,plain,
    ( m1_subset_1(sK1(sK2),u1_struct_0(sK2)) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v7_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_12,negated_conjecture,
    ( ~ v7_struct_0(sK2)
    | k3_yellow_0(sK2) != k4_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_776,negated_conjecture,
    ( ~ v7_struct_0(sK2)
    | k3_yellow_0(sK2) != k4_yellow_0(sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_786,plain,
    ( k3_yellow_0(sK2) != k4_yellow_0(sK2)
    | v7_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ v7_struct_0(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_347])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_struct_0(sK2)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_766,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK2))
    | ~ v7_struct_0(sK2)
    | X1_44 = X0_44 ),
    inference(subtyping,[status(esa)],[c_404])).

cnf(c_1159,plain,
    ( ~ m1_subset_1(k4_yellow_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2))
    | ~ v7_struct_0(sK2)
    | k3_yellow_0(sK2) = k4_yellow_0(sK2) ),
    inference(instantiation,[status(thm)],[c_766])).

cnf(c_1160,plain,
    ( k3_yellow_0(sK2) = k4_yellow_0(sK2)
    | m1_subset_1(k4_yellow_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_yellow_0(sK2),u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_1430,plain,
    ( m1_subset_1(sK1(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1061,c_21,c_35,c_38,c_41,c_50,c_786,c_1160])).

cnf(c_353,plain,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_354,plain,
    ( m1_subset_1(k4_yellow_0(sK2),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_771,plain,
    ( m1_subset_1(k4_yellow_0(sK2),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_354])).

cnf(c_1058,plain,
    ( m1_subset_1(k4_yellow_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X1 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_313,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_314,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ r1_orders_2(sK2,X0,X1)
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_14])).

cnf(c_319,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK2,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_772,plain,
    ( ~ r1_orders_2(sK2,X0_44,X1_44)
    | ~ r1_orders_2(sK2,X1_44,X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_44,u1_struct_0(sK2))
    | X0_44 = X1_44 ),
    inference(subtyping,[status(esa)],[c_319])).

cnf(c_1057,plain,
    ( X0_44 = X1_44
    | r1_orders_2(sK2,X0_44,X1_44) != iProver_top
    | r1_orders_2(sK2,X1_44,X0_44) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1_44,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_1265,plain,
    ( k4_yellow_0(sK2) = X0_44
    | r1_orders_2(sK2,X0_44,k4_yellow_0(sK2)) != iProver_top
    | r1_orders_2(sK2,k4_yellow_0(sK2),X0_44) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1058,c_1057])).

cnf(c_11,plain,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_yellow_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v3_yellow_0(X0)
    | v2_yellow_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( v3_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_256,plain,
    ( ~ l1_orders_2(X0)
    | v2_yellow_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_257,plain,
    ( ~ l1_orders_2(sK2)
    | v2_yellow_0(sK2) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_58,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v3_yellow_0(sK2)
    | v2_yellow_0(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_259,plain,
    ( v2_yellow_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_257,c_15,c_14,c_58])).

cnf(c_271,plain,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_259])).

cnf(c_272,plain,
    ( r1_orders_2(sK2,X0,k4_yellow_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_orders_2(sK2,X0,k4_yellow_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_17,c_16,c_14])).

cnf(c_277,plain,
    ( r1_orders_2(sK2,X0,k4_yellow_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_774,plain,
    ( r1_orders_2(sK2,X0_44,k4_yellow_0(sK2))
    | ~ m1_subset_1(X0_44,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_277])).

cnf(c_788,plain,
    ( r1_orders_2(sK2,X0_44,k4_yellow_0(sK2)) = iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_1530,plain,
    ( k4_yellow_0(sK2) = X0_44
    | r1_orders_2(sK2,k4_yellow_0(sK2),X0_44) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1265,c_788])).

cnf(c_13,negated_conjecture,
    ( v7_struct_0(sK2)
    | k3_yellow_0(sK2) = k4_yellow_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_775,negated_conjecture,
    ( v7_struct_0(sK2)
    | k3_yellow_0(sK2) = k4_yellow_0(sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1054,plain,
    ( k3_yellow_0(sK2) = k4_yellow_0(sK2)
    | v7_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_1063,plain,
    ( X0_44 = X1_44
    | m1_subset_1(X1_44,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_1453,plain,
    ( v7_struct_0(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1063,c_21,c_38,c_41,c_786,c_1160])).

cnf(c_1458,plain,
    ( k4_yellow_0(sK2) = k3_yellow_0(sK2) ),
    inference(superposition,[status(thm)],[c_1054,c_1453])).

cnf(c_1536,plain,
    ( k4_yellow_0(sK2) = X0_44
    | r1_orders_2(sK2,k3_yellow_0(sK2),X0_44) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1530,c_1458])).

cnf(c_1537,plain,
    ( k3_yellow_0(sK2) = X0_44
    | r1_orders_2(sK2,k3_yellow_0(sK2),X0_44) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1536,c_1458])).

cnf(c_10,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | ~ v3_yellow_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_245,plain,
    ( v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_246,plain,
    ( v1_yellow_0(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_55,plain,
    ( v1_yellow_0(sK2)
    | ~ l1_orders_2(sK2)
    | ~ v3_yellow_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_248,plain,
    ( v1_yellow_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_246,c_15,c_14,c_55])).

cnf(c_292,plain,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_248])).

cnf(c_293,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r1_orders_2(sK2,k3_yellow_0(sK2),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_293,c_17,c_16,c_14])).

cnf(c_298,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_773,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),X0_44)
    | ~ m1_subset_1(X0_44,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_298])).

cnf(c_1056,plain,
    ( r1_orders_2(sK2,k3_yellow_0(sK2),X0_44) = iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_1541,plain,
    ( k3_yellow_0(sK2) = X0_44
    | m1_subset_1(X0_44,u1_struct_0(sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1537,c_1056])).

cnf(c_1547,plain,
    ( k3_yellow_0(sK2) = sK1(sK2) ),
    inference(superposition,[status(thm)],[c_1430,c_1541])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_373,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | v7_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_347])).

cnf(c_374,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | v7_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_769,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | v7_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_1060,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2)) = iProver_top
    | v7_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_45,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0)) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v7_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_47,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2)) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v7_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_1420,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1060,c_21,c_35,c_38,c_41,c_47,c_786,c_1160])).

cnf(c_1546,plain,
    ( k3_yellow_0(sK2) = sK0(sK2) ),
    inference(superposition,[status(thm)],[c_1420,c_1541])).

cnf(c_1756,plain,
    ( sK1(sK2) = sK0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1547,c_1546])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | v7_struct_0(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_393,plain,
    ( v7_struct_0(X0)
    | sK1(X0) != sK0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_347])).

cnf(c_394,plain,
    ( v7_struct_0(sK2)
    | sK1(sK2) != sK0(sK2) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_767,plain,
    ( v7_struct_0(sK2)
    | sK1(sK2) != sK0(sK2) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_1062,plain,
    ( sK1(sK2) != sK0(sK2)
    | v7_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_799,plain,
    ( sK1(sK2) != sK0(sK2)
    | v7_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_1290,plain,
    ( sK1(sK2) != sK0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_21,c_38,c_41,c_786,c_799,c_1160])).

cnf(c_1758,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1756,c_1290])).


%------------------------------------------------------------------------------
