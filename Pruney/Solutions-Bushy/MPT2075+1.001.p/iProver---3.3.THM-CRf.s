%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2075+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:09 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_43)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f10,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f11,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f16,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f17,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK4(X3))
        & m1_subset_1(sK4(X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK3,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK3,X0)
        & v7_waybel_0(sK3)
        & v4_orders_2(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( ~ r3_waybel_9(sK2,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
            & l1_waybel_0(X1,sK2)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK2) )
      & ( ! [X3] :
            ( ? [X4] :
                ( r3_waybel_9(sK2,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK2)) )
            | ~ l1_waybel_0(X3,sK2)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK2) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ( ! [X2] :
            ( ~ r3_waybel_9(sK2,sK3,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK2)) )
        & l1_waybel_0(sK3,sK2)
        & v7_waybel_0(sK3)
        & v4_orders_2(sK3)
        & ~ v2_struct_0(sK3) )
      | ~ v1_compts_1(sK2) )
    & ( ! [X3] :
          ( ( r3_waybel_9(sK2,X3,sK4(X3))
            & m1_subset_1(sK4(X3),u1_struct_0(sK2)) )
          | ~ l1_waybel_0(X3,sK2)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK2) )
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f21,f20,f19])).

fof(f33,plain,(
    ! [X3] :
      ( m1_subset_1(sK4(X3),u1_struct_0(sK2))
      | ~ l1_waybel_0(X3,sK2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) )
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r3_waybel_9(X0,X1,X2) ) )
       => v1_compts_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f8,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK1(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK1(X0),X0)
        & v7_waybel_0(sK1(X0))
        & v4_orders_2(sK1(X0))
        & ~ v2_struct_0(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK1(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK1(X0),X0)
        & v7_waybel_0(sK1(X0))
        & v4_orders_2(sK1(X0))
        & ~ v2_struct_0(sK1(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f14])).

fof(f28,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK1(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,
    ( l1_waybel_0(sK3,sK2)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK0(X0,X1))
            & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,
    ( ~ v2_struct_0(sK3)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,
    ( v4_orders_2(sK3)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,
    ( v7_waybel_0(sK3)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X2] :
      ( ~ r3_waybel_9(sK2,sK3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | ~ v1_compts_1(sK2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X3] :
      ( r3_waybel_9(sK2,X3,sK4(X3))
      | ~ l1_waybel_0(X3,sK2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK1(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4(X0),u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( l1_waybel_0(sK1(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_216,plain,
    ( l1_waybel_0(sK1(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_3,c_14])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_218,plain,
    ( v1_compts_1(sK2)
    | l1_waybel_0(sK1(sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_16,c_15,c_14,c_43])).

cnf(c_219,plain,
    ( l1_waybel_0(sK1(sK2),sK2)
    | v1_compts_1(sK2) ),
    inference(renaming,[status(thm)],[c_218])).

cnf(c_383,plain,
    ( m1_subset_1(sK4(sK1(sK2)),u1_struct_0(sK2))
    | v1_compts_1(sK2)
    | v2_struct_0(sK1(sK2))
    | ~ v4_orders_2(sK1(sK2))
    | ~ v7_waybel_0(sK1(sK2)) ),
    inference(resolution,[status(thm)],[c_13,c_219])).

cnf(c_8,negated_conjecture,
    ( l1_waybel_0(sK3,sK2)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_249,plain,
    ( m1_subset_1(sK0(sK2,X0),u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ v1_compts_1(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_1,c_14])).

cnf(c_253,plain,
    ( v2_struct_0(X0)
    | ~ v1_compts_1(sK2)
    | m1_subset_1(sK0(sK2,X0),u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_16,c_15])).

cnf(c_254,plain,
    ( m1_subset_1(sK0(sK2,X0),u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v1_compts_1(sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_371,plain,
    ( m1_subset_1(sK0(sK2,sK3),u1_struct_0(sK2))
    | ~ v1_compts_1(sK2)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK3) ),
    inference(resolution,[status(thm)],[c_8,c_254])).

cnf(c_11,negated_conjecture,
    ( ~ v1_compts_1(sK2)
    | ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,negated_conjecture,
    ( ~ v1_compts_1(sK2)
    | v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9,negated_conjecture,
    ( ~ v1_compts_1(sK2)
    | v7_waybel_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,negated_conjecture,
    ( ~ r3_waybel_9(sK2,sK3,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( r3_waybel_9(X0,X1,sK0(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_278,plain,
    ( r3_waybel_9(sK2,X0,sK0(sK2,X0))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ v1_compts_1(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_0,c_14])).

cnf(c_282,plain,
    ( v2_struct_0(X0)
    | ~ v1_compts_1(sK2)
    | r3_waybel_9(sK2,X0,sK0(sK2,X0))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_278,c_16,c_15])).

cnf(c_283,plain,
    ( r3_waybel_9(sK2,X0,sK0(sK2,X0))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v1_compts_1(sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_282])).

cnf(c_338,plain,
    ( ~ m1_subset_1(sK0(sK2,sK3),u1_struct_0(sK2))
    | ~ l1_waybel_0(sK3,sK2)
    | ~ v1_compts_1(sK2)
    | v2_struct_0(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v7_waybel_0(sK3) ),
    inference(resolution,[status(thm)],[c_7,c_283])).

cnf(c_340,plain,
    ( ~ v1_compts_1(sK2)
    | ~ m1_subset_1(sK0(sK2,sK3),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_11,c_10,c_9,c_8])).

cnf(c_341,plain,
    ( ~ m1_subset_1(sK0(sK2,sK3),u1_struct_0(sK2))
    | ~ v1_compts_1(sK2) ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_373,plain,
    ( ~ v1_compts_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_11,c_10,c_9,c_341])).

cnf(c_12,negated_conjecture,
    ( r3_waybel_9(sK2,X0,sK4(X0))
    | ~ l1_waybel_0(X0,sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( ~ r3_waybel_9(X0,sK1(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_229,plain,
    ( ~ r3_waybel_9(sK2,sK1(sK2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_2,c_14])).

cnf(c_233,plain,
    ( v1_compts_1(sK2)
    | ~ r3_waybel_9(sK2,sK1(sK2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_229,c_16,c_15])).

cnf(c_234,plain,
    ( ~ r3_waybel_9(sK2,sK1(sK2),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v1_compts_1(sK2) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_351,plain,
    ( ~ m1_subset_1(sK4(sK1(sK2)),u1_struct_0(sK2))
    | ~ l1_waybel_0(sK1(sK2),sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK1(sK2))
    | ~ v4_orders_2(sK1(sK2))
    | ~ v7_waybel_0(sK1(sK2)) ),
    inference(resolution,[status(thm)],[c_12,c_234])).

cnf(c_6,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_177,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_compts_1(sK2)
    | ~ v2_struct_0(sK1(sK2))
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_6,c_14])).

cnf(c_179,plain,
    ( ~ v2_struct_0(sK1(sK2))
    | v1_compts_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_177,c_16,c_15])).

cnf(c_180,plain,
    ( v1_compts_1(sK2)
    | ~ v2_struct_0(sK1(sK2)) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_5,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK1(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_190,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK2)
    | v4_orders_2(sK1(sK2)) ),
    inference(resolution,[status(thm)],[c_5,c_14])).

cnf(c_192,plain,
    ( v1_compts_1(sK2)
    | v4_orders_2(sK1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_190,c_16,c_15])).

cnf(c_4,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_203,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK2)
    | v7_waybel_0(sK1(sK2)) ),
    inference(resolution,[status(thm)],[c_4,c_14])).

cnf(c_40,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_compts_1(sK2)
    | v2_struct_0(sK2)
    | v7_waybel_0(sK1(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_205,plain,
    ( v1_compts_1(sK2)
    | v7_waybel_0(sK1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_203,c_16,c_15,c_14,c_40])).

cnf(c_353,plain,
    ( v1_compts_1(sK2)
    | ~ m1_subset_1(sK4(sK1(sK2)),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_351,c_16,c_15,c_14,c_40,c_43,c_180,c_190])).

cnf(c_354,plain,
    ( ~ m1_subset_1(sK4(sK1(sK2)),u1_struct_0(sK2))
    | v1_compts_1(sK2) ),
    inference(renaming,[status(thm)],[c_353])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_383,c_373,c_354,c_205,c_192,c_180])).


%------------------------------------------------------------------------------
