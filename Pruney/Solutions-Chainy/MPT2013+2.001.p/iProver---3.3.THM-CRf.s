%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:40 EST 2020

% Result     : Theorem 51.61s
% Output     : CNFRefutation 51.61s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_26762)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r1_orders_2(X2,X3,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X5] :
              ( r1_orders_2(X2,X3,X5)
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X3,X2,X0] :
      ( ? [X5] :
          ( r1_orders_2(X2,X3,X5)
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( r1_orders_2(X2,X3,sK6(X0,X2,X3))
        & sK6(X0,X2,X3) = X0
        & m1_subset_1(sK6(X0,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ( r1_orders_2(X2,X3,sK6(X0,X2,X3))
            & sK6(X0,X2,X3) = X0
            & m1_subset_1(sK6(X0,X2,X3),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ r1_orders_2(X2,X3,X4)
      | X0 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,a_3_0_waybel_9(X1,X2,X3))
      | ~ r1_orders_2(X2,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( u1_struct_0(k4_waybel_9(X0,X1,sK9)) != a_3_0_waybel_9(X0,X1,sK9)
        & m1_subset_1(sK9,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( u1_struct_0(k4_waybel_9(X0,sK8,X2)) != a_3_0_waybel_9(X0,sK8,X2)
            & m1_subset_1(X2,u1_struct_0(sK8)) )
        & l1_waybel_0(sK8,X0)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(sK7,X1,X2)) != a_3_0_waybel_9(sK7,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK7)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != a_3_0_waybel_9(sK7,sK8,sK9)
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l1_waybel_0(sK8,sK7)
    & ~ v2_struct_0(sK8)
    & l1_struct_0(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f16,f41,f40,f39])).

fof(f69,plain,(
    l1_struct_0(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f18,plain,(
    ! [X2,X0,X1,X3] :
      ( ( k4_waybel_9(X0,X1,X2) = X3
      <=> sP0(X3,X1,X0,X2) )
      | ~ sP1(X2,X0,X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X3,X1,X0,X2] :
      ( sP0(X3,X1,X0,X2)
    <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        & ! [X4] :
            ( r2_hidden(X4,u1_struct_0(X3))
          <=> ? [X5] :
                ( r1_orders_2(X1,X2,X5)
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X2,X0,X1,X3)
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f10,f18,f17])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X0,X1,X3)
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X2,X0,X1,X3] :
      ( ( ( k4_waybel_9(X0,X1,X2) = X3
          | ~ sP0(X3,X1,X0,X2) )
        & ( sP0(X3,X1,X0,X2)
          | k4_waybel_9(X0,X1,X2) != X3 ) )
      | ~ sP1(X2,X0,X1,X3) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k4_waybel_9(X1,X2,X0) = X3
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k4_waybel_9(X1,X2,X0) != X3 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f26])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k4_waybel_9(X1,X2,X0) != X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0)
      | ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f28,plain,(
    ! [X3,X1,X0,X2] :
      ( ( sP0(X3,X1,X0,X2)
        | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_orders_2(X1,X2,X5)
                  | X4 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r2_hidden(X4,u1_struct_0(X3)) )
            & ( ? [X5] :
                  ( r1_orders_2(X1,X2,X5)
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X4,u1_struct_0(X3)) ) ) )
      & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
          & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
          & ! [X4] :
              ( ( r2_hidden(X4,u1_struct_0(X3))
                | ! [X5] :
                    ( ~ r1_orders_2(X1,X2,X5)
                    | X4 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( r1_orders_2(X1,X2,X5)
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
        | ~ sP0(X3,X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X3,X1,X0,X2] :
      ( ( sP0(X3,X1,X0,X2)
        | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
        | ~ r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_orders_2(X1,X2,X5)
                  | X4 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r2_hidden(X4,u1_struct_0(X3)) )
            & ( ? [X5] :
                  ( r1_orders_2(X1,X2,X5)
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              | r2_hidden(X4,u1_struct_0(X3)) ) ) )
      & ( ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
          & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
          & ! [X4] :
              ( ( r2_hidden(X4,u1_struct_0(X3))
                | ! [X5] :
                    ( ~ r1_orders_2(X1,X2,X5)
                    | X4 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( r1_orders_2(X1,X2,X5)
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_hidden(X4,u1_struct_0(X3)) ) ) )
        | ~ sP0(X3,X1,X0,X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
        | ~ r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_orders_2(X1,X3,X5)
                  | X4 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              | ~ r2_hidden(X4,u1_struct_0(X0)) )
            & ( ? [X6] :
                  ( r1_orders_2(X1,X3,X6)
                  & X4 = X6
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              | r2_hidden(X4,u1_struct_0(X0)) ) ) )
      & ( ( u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
          & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
          & ! [X7] :
              ( ( r2_hidden(X7,u1_struct_0(X0))
                | ! [X8] :
                    ( ~ r1_orders_2(X1,X3,X8)
                    | X7 != X8
                    | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
              & ( ? [X9] :
                    ( r1_orders_2(X1,X3,X9)
                    & X7 = X9
                    & m1_subset_1(X9,u1_struct_0(X1)) )
                | ~ r2_hidden(X7,u1_struct_0(X0)) ) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X7,X3,X1] :
      ( ? [X9] :
          ( r1_orders_2(X1,X3,X9)
          & X7 = X9
          & m1_subset_1(X9,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X3,sK5(X1,X3,X7))
        & sK5(X1,X3,X7) = X7
        & m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X4,X3,X1,X0] :
      ( ? [X6] :
          ( r1_orders_2(X1,X3,X6)
          & X4 = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X3,sK4(X0,X1,X3))
        & sK4(X0,X1,X3) = X4
        & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X3,X5)
                | X4 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X4,u1_struct_0(X0)) )
          & ( ? [X6] :
                ( r1_orders_2(X1,X3,X6)
                & X4 = X6
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | r2_hidden(X4,u1_struct_0(X0)) ) )
     => ( ( ! [X5] :
              ( ~ r1_orders_2(X1,X3,X5)
              | sK3(X0,X1,X3) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0)) )
        & ( ? [X6] :
              ( r1_orders_2(X1,X3,X6)
              & sK3(X0,X1,X3) = X6
              & m1_subset_1(X6,u1_struct_0(X1)) )
          | r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
        | ~ r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
        | ( ( ! [X5] :
                ( ~ r1_orders_2(X1,X3,X5)
                | sK3(X0,X1,X3) != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0)) )
          & ( ( r1_orders_2(X1,X3,sK4(X0,X1,X3))
              & sK3(X0,X1,X3) = sK4(X0,X1,X3)
              & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X1)) )
            | r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0)) ) ) )
      & ( ( u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0))
          & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)))
          & ! [X7] :
              ( ( r2_hidden(X7,u1_struct_0(X0))
                | ! [X8] :
                    ( ~ r1_orders_2(X1,X3,X8)
                    | X7 != X8
                    | ~ m1_subset_1(X8,u1_struct_0(X1)) ) )
              & ( ( r1_orders_2(X1,X3,sK5(X1,X3,X7))
                  & sK5(X1,X3,X7) = X7
                  & m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1)) )
                | ~ r2_hidden(X7,u1_struct_0(X0)) ) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f52,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK5(X1,X3,X7) = X7
      | ~ r2_hidden(X7,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sK6(X0,X2,X3) = X0
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    l1_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X2,X3),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X2,X3,sK6(X0,X2,X3))
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,u1_struct_0(X0))
      | ~ r1_orders_2(X1,X3,X8)
      | X7 != X8
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,u1_struct_0(X0))
      | ~ r1_orders_2(X1,X3,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X1))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( r1_orders_2(X1,X3,sK5(X1,X3,X7))
      | ~ r2_hidden(X7,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1))
      | ~ r2_hidden(X7,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

cnf(c_21,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_waybel_0(X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
    | ~ l1_struct_0(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK7) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_700,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_waybel_0(X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_701,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_705,plain,
    ( v2_struct_0(X0)
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_orders_2(X0,X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_701,c_30])).

cnf(c_706,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_705])).

cnf(c_77434,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_77641,plain,
    ( ~ r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_77434])).

cnf(c_77642,plain,
    ( r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77641])).

cnf(c_2193,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2217,plain,
    ( r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2206,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_18,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ v6_waybel_0(X3,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_332,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X4,X5)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | X5 != X1
    | k4_waybel_9(X5,X4,X6) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_333,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(k4_waybel_9(X1,X3,X4),X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_19,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_357,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_333,c_19])).

cnf(c_572,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_357,c_29])).

cnf(c_573,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3))
    | ~ l1_waybel_0(X1,sK7)
    | ~ l1_waybel_0(X2,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_577,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_573,c_30])).

cnf(c_578,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3))
    | ~ l1_waybel_0(X2,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_577])).

cnf(c_2198,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3)) = iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))
    | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2212,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0)) != iProver_top
    | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3153,plain,
    ( sP0(k4_waybel_9(sK7,X0,X1),X0,sK7,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_2212])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,u1_struct_0(X0))
    | sK5(X1,X3,X4) = X4 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2208,plain,
    ( sK5(X0,X1,X2) = X2
    | sP0(X3,X0,X4,X1) != iProver_top
    | r2_hidden(X2,u1_struct_0(X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3251,plain,
    ( sK5(X0,X1,X2) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_2208])).

cnf(c_4420,plain,
    ( sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_3251])).

cnf(c_23,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | sK6(X3,X0,X2) = X3 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_628,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6(X3,X0,X2) = X3
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_629,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | sK6(X2,X0,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_633,plain,
    ( v2_struct_0(X0)
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK7)
    | sK6(X2,X0,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_30])).

cnf(c_634,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | sK6(X2,X0,X1) = X2 ),
    inference(renaming,[status(thm)],[c_633])).

cnf(c_2196,plain,
    ( sK6(X0,X1,X2) = X0
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_3_0_waybel_9(sK7,X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_2673,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_2196])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2215,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2893,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | a_3_0_waybel_9(sK7,X0,X1) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2673,c_2215])).

cnf(c_5353,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3))),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3)))
    | sK5(X2,X3,sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))) = sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))
    | u1_struct_0(k4_waybel_9(sK7,X2,X3)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4420,c_2893])).

cnf(c_70682,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_5353])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,plain,
    ( v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,plain,
    ( l1_waybel_0(sK8,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_70725,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_70682,c_33,c_34])).

cnf(c_70726,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_70725])).

cnf(c_70731,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_70726])).

cnf(c_25,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_70742,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_70731])).

cnf(c_70818,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_70731,c_28,c_27,c_25,c_70742])).

cnf(c_70819,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(renaming,[status(thm)],[c_70818])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2216,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3146,plain,
    ( r2_hidden(sK2(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_2216])).

cnf(c_4300,plain,
    ( sK6(sK2(X0,X1),X2,X3) = sK2(X0,X1)
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,a_3_0_waybel_9(sK7,X2,X3)) != iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_2196])).

cnf(c_4428,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X3,X4) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4))
    | l1_waybel_0(X3,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X3)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2673,c_4300])).

cnf(c_17405,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_4428])).

cnf(c_17826,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17405,c_33,c_34])).

cnf(c_17827,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_17826])).

cnf(c_5352,plain,
    ( sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4420,c_2215])).

cnf(c_17868,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3)))
    | sK5(X2,X3,sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))) = sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))
    | u1_struct_0(k4_waybel_9(sK7,X2,X3)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_17827,c_5352])).

cnf(c_26062,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_17868])).

cnf(c_26752,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26062,c_33,c_34])).

cnf(c_26753,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_26752])).

cnf(c_26758,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_26753])).

cnf(c_26801,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26758,c_28,c_27,c_25,c_26762])).

cnf(c_26802,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(renaming,[status(thm)],[c_26801])).

cnf(c_24,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X3,X0,X2),u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_603,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X3,X0,X2),u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_604,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_608,plain,
    ( v2_struct_0(X0)
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_604,c_30])).

cnf(c_609,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_608])).

cnf(c_2197,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0)) = iProver_top
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_22,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
    | ~ l1_waybel_0(X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
    | ~ l1_struct_0(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_675,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
    | ~ l1_waybel_0(X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_676,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_680,plain,
    ( v2_struct_0(X0)
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK7)
    | r1_orders_2(X0,X1,sK6(X2,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_30])).

cnf(c_681,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_680])).

cnf(c_2194,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_3147,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X3) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_2216])).

cnf(c_3261,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | r1_orders_2(X0,X1,X3) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2673,c_3147])).

cnf(c_6514,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK6(X3,X0,X1),u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | r2_hidden(sK6(X3,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_3261])).

cnf(c_6702,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | r2_hidden(sK6(X3,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_6514])).

cnf(c_6929,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X3),X0,X1),X2) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X3) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_6702])).

cnf(c_7426,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),X3,X4) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4))
    | l1_waybel_0(X3,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X3)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6929,c_2196])).

cnf(c_8189,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_7426])).

cnf(c_8202,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8189,c_33,c_34])).

cnf(c_8203,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8202])).

cnf(c_8217,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3))),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3))),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(X2,X3,sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))) = sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))
    | u1_struct_0(k4_waybel_9(sK7,X2,X3)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8203,c_5352])).

cnf(c_32547,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_8217])).

cnf(c_32570,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32547,c_33,c_34])).

cnf(c_32571,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_32570])).

cnf(c_32576,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_32571])).

cnf(c_32582,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_32576])).

cnf(c_32622,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32576,c_28,c_27,c_25,c_32582])).

cnf(c_32623,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(renaming,[status(thm)],[c_32622])).

cnf(c_32624,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_32623,c_2197])).

cnf(c_35,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32639,plain,
    ( r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32624,c_33,c_34,c_35])).

cnf(c_32640,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_32639])).

cnf(c_32657,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26802,c_32640])).

cnf(c_2274,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK6(X1,sK8,X0),u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_2342,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | m1_subset_1(sK6(X0,sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2274])).

cnf(c_2564,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2342])).

cnf(c_2565,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2564])).

cnf(c_32739,plain,
    ( m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32657,c_33,c_34,c_35,c_2565])).

cnf(c_70825,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_70819,c_32739])).

cnf(c_71189,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_70825])).

cnf(c_32625,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_32623,c_2194])).

cnf(c_32841,plain,
    ( r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32625,c_33,c_34,c_35])).

cnf(c_32842,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_32841])).

cnf(c_32859,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26802,c_32842])).

cnf(c_2292,plain,
    ( r1_orders_2(sK8,X0,sK6(X1,sK8,X0))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_2374,plain,
    ( r1_orders_2(sK8,sK9,sK6(X0,sK8,sK9))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2292])).

cnf(c_2563,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_2567,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2563])).

cnf(c_32977,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32859,c_33,c_34,c_35,c_2567])).

cnf(c_70824,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_70819,c_32977])).

cnf(c_2280,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8)
    | sK6(X1,sK8,X0) = X1 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_2358,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | sK6(X0,sK8,sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_2280])).

cnf(c_2562,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_2569,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2562])).

cnf(c_1727,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7187,plain,
    ( sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_1728,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4418,plain,
    ( X0 != X1
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != X1
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = X0 ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_7194,plain,
    ( X0 != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = X0
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_4418])).

cnf(c_16969,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_7194])).

cnf(c_1735,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X3)
    | X3 != X2 ),
    theory(equality)).

cnf(c_2513,plain,
    ( ~ r1_orders_2(sK8,sK9,X0)
    | r1_orders_2(sK8,sK9,X1)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1735])).

cnf(c_4686,plain,
    ( r1_orders_2(sK8,sK9,X0)
    | ~ r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9))
    | X0 != sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2513])).

cnf(c_42661,plain,
    ( ~ r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9))
    | r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))))
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_4686])).

cnf(c_42663,plain,
    ( sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) != iProver_top
    | r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42661])).

cnf(c_71151,plain,
    ( r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_70824,c_33,c_34,c_35,c_2569,c_7187,c_16969,c_32977,c_42663])).

cnf(c_71155,plain,
    ( r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_71151])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | r2_hidden(X4,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2210,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_orders_2(X1,X3,X4) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X4,u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3892,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_2210])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2218,plain,
    ( r2_hidden(sK2(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5179,plain,
    ( r1_orders_2(X0,X1,sK2(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1)))) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK2(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))),u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3892,c_2218])).

cnf(c_72431,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_71155,c_5179])).

cnf(c_72438,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_71189,c_33,c_34,c_35,c_72431])).

cnf(c_72442,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_72438,c_2215])).

cnf(c_72481,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_72438,c_5352])).

cnf(c_72548,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_72442,c_33,c_34,c_35,c_25,c_72481])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_orders_2(X1,X3,sK5(X1,X3,X4))
    | ~ r2_hidden(X4,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2209,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_orders_2(X1,X3,sK5(X1,X3,X4)) = iProver_top
    | r2_hidden(X4,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3786,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X1,X2)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_2209])).

cnf(c_4903,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_3786])).

cnf(c_2627,plain,
    ( sK6(X0,X1,X2) = X0
    | r1_orders_2(X1,X2,X0) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_2196])).

cnf(c_5308,plain,
    ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4903,c_2627])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | m1_subset_1(sK5(X1,X3,X4),u1_struct_0(X1))
    | ~ r2_hidden(X4,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2207,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | m1_subset_1(sK5(X1,X3,X4),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X4,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3781,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) = iProver_top
    | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3153,c_2207])).

cnf(c_4896,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),u1_struct_0(X0)) = iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_3781])).

cnf(c_64538,plain,
    ( m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5308,c_4896])).

cnf(c_64539,plain,
    ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_64538])).

cnf(c_64544,plain,
    ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_64539,c_2215])).

cnf(c_64994,plain,
    ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,X2,X3))),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,X2,X3)))
    | sK6(sK2(a_3_0_waybel_9(sK7,X2,X3),a_3_0_waybel_9(sK7,sK8,sK9)),X2,X3) = sK2(a_3_0_waybel_9(sK7,X2,X3),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X2,X3),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X2,X3),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,X2,X3)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17827,c_64544])).

cnf(c_67028,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1)))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_64994])).

cnf(c_67063,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1)))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_67028,c_33,c_34])).

cnf(c_67064,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1)))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_67063])).

cnf(c_67069,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_67064])).

cnf(c_2255,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2306,plain,
    ( r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2415,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2593,plain,
    ( ~ sP0(X0,sK8,X1,X2)
    | m1_subset_1(sK5(sK8,X2,X3),u1_struct_0(sK8))
    | ~ r2_hidden(X3,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3129,plain,
    ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,X0,X1)
    | m1_subset_1(sK5(sK8,X1,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8))
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_2593])).

cnf(c_3368,plain,
    ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9)
    | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8))
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_3129])).

cnf(c_2806,plain,
    ( ~ sP0(X0,sK8,X1,sK9)
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,X2))
    | ~ r2_hidden(X2,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3847,plain,
    ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,X0,sK9)
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))))
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_2806])).

cnf(c_3849,plain,
    ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9)
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))))
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_3847])).

cnf(c_4148,plain,
    ( ~ sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9))
    | sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2286,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,sK8,X2))
    | ~ l1_waybel_0(X1,sK7)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | v2_struct_0(X1)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_3562,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,sK8,sK9))
    | ~ l1_waybel_0(X1,sK7)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | v2_struct_0(X1)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2286])).

cnf(c_4474,plain,
    ( sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3562])).

cnf(c_2299,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_2392,plain,
    ( ~ r1_orders_2(sK8,sK9,X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2299])).

cnf(c_2508,plain,
    ( ~ r1_orders_2(sK8,sK9,sK5(sK8,sK9,X0))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK5(sK8,sK9,X0),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(sK5(sK8,sK9,X0),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_5001,plain,
    ( ~ r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2508])).

cnf(c_9433,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_67268,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_67069,c_33,c_34,c_35,c_25,c_2256,c_2307,c_2416,c_2569,c_3369,c_3850,c_4149,c_4475,c_5002,c_9440])).

cnf(c_67269,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(renaming,[status(thm)],[c_67268])).

cnf(c_72558,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(demodulation,[status(thm)],[c_72548,c_67269])).

cnf(c_73055,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_72558,c_2197])).

cnf(c_2307,plain,
    ( r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2306])).

cnf(c_2414,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2418,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_2313,plain,
    ( ~ r1_tarski(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),X0)
    | a_3_0_waybel_9(sK7,sK8,sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2571,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | a_3_0_waybel_9(sK7,sK8,sK9) = u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_2313])).

cnf(c_2572,plain,
    ( a_3_0_waybel_9(sK7,sK8,sK9) = u1_struct_0(k4_waybel_9(sK7,sK8,sK9))
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2571])).

cnf(c_2258,plain,
    ( a_3_0_waybel_9(sK7,sK8,sK9) != X0
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != X0
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_3213,plain,
    ( a_3_0_waybel_9(sK7,sK8,sK9) != u1_struct_0(k4_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_4197,plain,
    ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_73206,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_73055,c_33,c_34,c_35,c_25,c_2307,c_2418,c_2569,c_2572,c_3213,c_4197])).

cnf(c_73207,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_73206])).

cnf(c_73210,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_73207])).

cnf(c_2815,plain,
    ( sK6(sK6(X0,X1,X2),X1,X2) = sK6(X0,X1,X2)
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_3_0_waybel_9(sK7,X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2194,c_2627])).

cnf(c_2898,plain,
    ( sK6(sK6(X0,X1,X2),X1,X2) = sK6(X0,X1,X2)
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_3_0_waybel_9(sK7,X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_2815])).

cnf(c_3006,plain,
    ( sK6(sK6(X0,X1,X2),X1,X2) = sK6(X0,X1,X2)
    | r1_orders_2(X1,X2,X0) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_2898])).

cnf(c_5307,plain,
    ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4903,c_3006])).

cnf(c_61628,plain,
    ( m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5307,c_4896])).

cnf(c_61629,plain,
    ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_61628])).

cnf(c_61634,plain,
    ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_61629,c_2215])).

cnf(c_62065,plain,
    ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,X2,X3))),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,X2,X3))),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X2,X3),a_3_0_waybel_9(sK7,sK8,sK9)),X2,X3) = sK2(a_3_0_waybel_9(sK7,X2,X3),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X2,X3),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X2,X3),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,X2,X3)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17827,c_61634])).

cnf(c_64317,plain,
    ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_62065])).

cnf(c_64358,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_64317,c_33,c_34])).

cnf(c_64359,plain,
    ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_64358])).

cnf(c_64364,plain,
    ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_64359])).

cnf(c_2256,plain,
    ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2255])).

cnf(c_2416,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2415])).

cnf(c_2584,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | a_3_0_waybel_9(sK7,sK8,sK9) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2313])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2832,plain,
    ( r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3369,plain,
    ( sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3368])).

cnf(c_3848,plain,
    ( sP0(k4_waybel_9(sK7,sK8,sK9),sK8,X0,sK9) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3847])).

cnf(c_3850,plain,
    ( sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3848])).

cnf(c_4149,plain,
    ( sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9)) != iProver_top
    | sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4148])).

cnf(c_4475,plain,
    ( sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4474])).

cnf(c_5002,plain,
    ( r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5001])).

cnf(c_9440,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9433])).

cnf(c_19455,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_1729,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2481,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,a_3_0_waybel_9(sK7,sK8,sK9))
    | X2 != X0
    | a_3_0_waybel_9(sK7,sK8,sK9) != X1 ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_2953,plain,
    ( ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,sK9))
    | X1 != X0
    | a_3_0_waybel_9(sK7,sK8,sK9) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_9432,plain,
    ( r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | X0 != sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | a_3_0_waybel_9(sK7,sK8,sK9) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2953])).

cnf(c_33482,plain,
    ( r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) != sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | a_3_0_waybel_9(sK7,sK8,sK9) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_9432])).

cnf(c_64391,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_64364,c_33,c_34,c_35,c_25,c_2256,c_2307,c_2416,c_2569,c_2584,c_2832,c_3369,c_3850,c_4149,c_4475,c_5002,c_9440,c_19462,c_33483])).

cnf(c_64392,plain,
    ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(renaming,[status(thm)],[c_64391])).

cnf(c_64394,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_64392,c_2197])).

cnf(c_9435,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2342])).

cnf(c_9436,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9435])).

cnf(c_66639,plain,
    ( m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_64394,c_33,c_34,c_35,c_25,c_2307,c_2416,c_2569,c_2572,c_3213,c_3369,c_3850,c_4149,c_4197,c_4475,c_5002,c_9436])).

cnf(c_66640,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_66639])).

cnf(c_67282,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_67269,c_66640])).

cnf(c_72556,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_72548,c_67282])).

cnf(c_72566,plain,
    ( m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_72556])).

cnf(c_64395,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_64392,c_2194])).

cnf(c_9434,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_9438,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9434])).

cnf(c_66806,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_64395,c_33,c_34,c_35,c_25,c_2256,c_2307,c_2416,c_2569,c_3369,c_3850,c_4149,c_4475,c_5002,c_9438])).

cnf(c_67281,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_67269,c_66806])).

cnf(c_72557,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_72548,c_67281])).

cnf(c_72567,plain,
    ( r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_72557])).

cnf(c_73213,plain,
    ( ~ r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_73210])).

cnf(c_73277,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_73210,c_28,c_27,c_26,c_72566,c_72567,c_73213])).

cnf(c_73281,plain,
    ( m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_73277,c_32739])).

cnf(c_72573,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_72548,c_4896])).

cnf(c_72572,plain,
    ( r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_72548,c_4903])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_77642,c_73281,c_72573,c_72572,c_72431,c_2418,c_2307,c_2256,c_25,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 51.61/7.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.61/7.02  
% 51.61/7.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.61/7.02  
% 51.61/7.02  ------  iProver source info
% 51.61/7.02  
% 51.61/7.02  git: date: 2020-06-30 10:37:57 +0100
% 51.61/7.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.61/7.02  git: non_committed_changes: false
% 51.61/7.02  git: last_make_outside_of_git: false
% 51.61/7.02  
% 51.61/7.02  ------ 
% 51.61/7.02  
% 51.61/7.02  ------ Input Options
% 51.61/7.02  
% 51.61/7.02  --out_options                           all
% 51.61/7.02  --tptp_safe_out                         true
% 51.61/7.02  --problem_path                          ""
% 51.61/7.02  --include_path                          ""
% 51.61/7.02  --clausifier                            res/vclausify_rel
% 51.61/7.02  --clausifier_options                    ""
% 51.61/7.02  --stdin                                 false
% 51.61/7.02  --stats_out                             all
% 51.61/7.02  
% 51.61/7.02  ------ General Options
% 51.61/7.02  
% 51.61/7.02  --fof                                   false
% 51.61/7.02  --time_out_real                         305.
% 51.61/7.02  --time_out_virtual                      -1.
% 51.61/7.02  --symbol_type_check                     false
% 51.61/7.02  --clausify_out                          false
% 51.61/7.02  --sig_cnt_out                           false
% 51.61/7.02  --trig_cnt_out                          false
% 51.61/7.02  --trig_cnt_out_tolerance                1.
% 51.61/7.02  --trig_cnt_out_sk_spl                   false
% 51.61/7.02  --abstr_cl_out                          false
% 51.61/7.02  
% 51.61/7.02  ------ Global Options
% 51.61/7.02  
% 51.61/7.02  --schedule                              default
% 51.61/7.02  --add_important_lit                     false
% 51.61/7.02  --prop_solver_per_cl                    1000
% 51.61/7.02  --min_unsat_core                        false
% 51.61/7.02  --soft_assumptions                      false
% 51.61/7.02  --soft_lemma_size                       3
% 51.61/7.02  --prop_impl_unit_size                   0
% 51.61/7.02  --prop_impl_unit                        []
% 51.61/7.02  --share_sel_clauses                     true
% 51.61/7.02  --reset_solvers                         false
% 51.61/7.02  --bc_imp_inh                            [conj_cone]
% 51.61/7.02  --conj_cone_tolerance                   3.
% 51.61/7.02  --extra_neg_conj                        none
% 51.61/7.02  --large_theory_mode                     true
% 51.61/7.02  --prolific_symb_bound                   200
% 51.61/7.02  --lt_threshold                          2000
% 51.61/7.02  --clause_weak_htbl                      true
% 51.61/7.02  --gc_record_bc_elim                     false
% 51.61/7.02  
% 51.61/7.02  ------ Preprocessing Options
% 51.61/7.02  
% 51.61/7.02  --preprocessing_flag                    true
% 51.61/7.02  --time_out_prep_mult                    0.1
% 51.61/7.02  --splitting_mode                        input
% 51.61/7.02  --splitting_grd                         true
% 51.61/7.02  --splitting_cvd                         false
% 51.61/7.02  --splitting_cvd_svl                     false
% 51.61/7.02  --splitting_nvd                         32
% 51.61/7.02  --sub_typing                            true
% 51.61/7.02  --prep_gs_sim                           true
% 51.61/7.02  --prep_unflatten                        true
% 51.61/7.02  --prep_res_sim                          true
% 51.61/7.02  --prep_upred                            true
% 51.61/7.02  --prep_sem_filter                       exhaustive
% 51.61/7.02  --prep_sem_filter_out                   false
% 51.61/7.02  --pred_elim                             true
% 51.61/7.02  --res_sim_input                         true
% 51.61/7.02  --eq_ax_congr_red                       true
% 51.61/7.02  --pure_diseq_elim                       true
% 51.61/7.02  --brand_transform                       false
% 51.61/7.02  --non_eq_to_eq                          false
% 51.61/7.02  --prep_def_merge                        true
% 51.61/7.02  --prep_def_merge_prop_impl              false
% 51.61/7.02  --prep_def_merge_mbd                    true
% 51.61/7.02  --prep_def_merge_tr_red                 false
% 51.61/7.02  --prep_def_merge_tr_cl                  false
% 51.61/7.02  --smt_preprocessing                     true
% 51.61/7.02  --smt_ac_axioms                         fast
% 51.61/7.02  --preprocessed_out                      false
% 51.61/7.02  --preprocessed_stats                    false
% 51.61/7.02  
% 51.61/7.02  ------ Abstraction refinement Options
% 51.61/7.02  
% 51.61/7.02  --abstr_ref                             []
% 51.61/7.02  --abstr_ref_prep                        false
% 51.61/7.02  --abstr_ref_until_sat                   false
% 51.61/7.02  --abstr_ref_sig_restrict                funpre
% 51.61/7.02  --abstr_ref_af_restrict_to_split_sk     false
% 51.61/7.02  --abstr_ref_under                       []
% 51.61/7.02  
% 51.61/7.02  ------ SAT Options
% 51.61/7.02  
% 51.61/7.02  --sat_mode                              false
% 51.61/7.02  --sat_fm_restart_options                ""
% 51.61/7.02  --sat_gr_def                            false
% 51.61/7.02  --sat_epr_types                         true
% 51.61/7.02  --sat_non_cyclic_types                  false
% 51.61/7.02  --sat_finite_models                     false
% 51.61/7.02  --sat_fm_lemmas                         false
% 51.61/7.02  --sat_fm_prep                           false
% 51.61/7.02  --sat_fm_uc_incr                        true
% 51.61/7.02  --sat_out_model                         small
% 51.61/7.02  --sat_out_clauses                       false
% 51.61/7.02  
% 51.61/7.02  ------ QBF Options
% 51.61/7.02  
% 51.61/7.02  --qbf_mode                              false
% 51.61/7.02  --qbf_elim_univ                         false
% 51.61/7.02  --qbf_dom_inst                          none
% 51.61/7.02  --qbf_dom_pre_inst                      false
% 51.61/7.02  --qbf_sk_in                             false
% 51.61/7.02  --qbf_pred_elim                         true
% 51.61/7.02  --qbf_split                             512
% 51.61/7.02  
% 51.61/7.02  ------ BMC1 Options
% 51.61/7.02  
% 51.61/7.02  --bmc1_incremental                      false
% 51.61/7.02  --bmc1_axioms                           reachable_all
% 51.61/7.02  --bmc1_min_bound                        0
% 51.61/7.02  --bmc1_max_bound                        -1
% 51.61/7.02  --bmc1_max_bound_default                -1
% 51.61/7.02  --bmc1_symbol_reachability              true
% 51.61/7.02  --bmc1_property_lemmas                  false
% 51.61/7.02  --bmc1_k_induction                      false
% 51.61/7.02  --bmc1_non_equiv_states                 false
% 51.61/7.02  --bmc1_deadlock                         false
% 51.61/7.02  --bmc1_ucm                              false
% 51.61/7.02  --bmc1_add_unsat_core                   none
% 51.61/7.02  --bmc1_unsat_core_children              false
% 51.61/7.02  --bmc1_unsat_core_extrapolate_axioms    false
% 51.61/7.02  --bmc1_out_stat                         full
% 51.61/7.02  --bmc1_ground_init                      false
% 51.61/7.02  --bmc1_pre_inst_next_state              false
% 51.61/7.02  --bmc1_pre_inst_state                   false
% 51.61/7.02  --bmc1_pre_inst_reach_state             false
% 51.61/7.02  --bmc1_out_unsat_core                   false
% 51.61/7.02  --bmc1_aig_witness_out                  false
% 51.61/7.02  --bmc1_verbose                          false
% 51.61/7.02  --bmc1_dump_clauses_tptp                false
% 51.61/7.02  --bmc1_dump_unsat_core_tptp             false
% 51.61/7.02  --bmc1_dump_file                        -
% 51.61/7.02  --bmc1_ucm_expand_uc_limit              128
% 51.61/7.02  --bmc1_ucm_n_expand_iterations          6
% 51.61/7.02  --bmc1_ucm_extend_mode                  1
% 51.61/7.02  --bmc1_ucm_init_mode                    2
% 51.61/7.02  --bmc1_ucm_cone_mode                    none
% 51.61/7.02  --bmc1_ucm_reduced_relation_type        0
% 51.61/7.02  --bmc1_ucm_relax_model                  4
% 51.61/7.02  --bmc1_ucm_full_tr_after_sat            true
% 51.61/7.02  --bmc1_ucm_expand_neg_assumptions       false
% 51.61/7.02  --bmc1_ucm_layered_model                none
% 51.61/7.02  --bmc1_ucm_max_lemma_size               10
% 51.61/7.02  
% 51.61/7.02  ------ AIG Options
% 51.61/7.02  
% 51.61/7.02  --aig_mode                              false
% 51.61/7.02  
% 51.61/7.02  ------ Instantiation Options
% 51.61/7.02  
% 51.61/7.02  --instantiation_flag                    true
% 51.61/7.02  --inst_sos_flag                         true
% 51.61/7.02  --inst_sos_phase                        true
% 51.61/7.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.61/7.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.61/7.02  --inst_lit_sel_side                     num_symb
% 51.61/7.02  --inst_solver_per_active                1400
% 51.61/7.02  --inst_solver_calls_frac                1.
% 51.61/7.02  --inst_passive_queue_type               priority_queues
% 51.61/7.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.61/7.02  --inst_passive_queues_freq              [25;2]
% 51.61/7.02  --inst_dismatching                      true
% 51.61/7.02  --inst_eager_unprocessed_to_passive     true
% 51.61/7.02  --inst_prop_sim_given                   true
% 51.61/7.02  --inst_prop_sim_new                     false
% 51.61/7.02  --inst_subs_new                         false
% 51.61/7.02  --inst_eq_res_simp                      false
% 51.61/7.02  --inst_subs_given                       false
% 51.61/7.02  --inst_orphan_elimination               true
% 51.61/7.02  --inst_learning_loop_flag               true
% 51.61/7.02  --inst_learning_start                   3000
% 51.61/7.02  --inst_learning_factor                  2
% 51.61/7.02  --inst_start_prop_sim_after_learn       3
% 51.61/7.02  --inst_sel_renew                        solver
% 51.61/7.02  --inst_lit_activity_flag                true
% 51.61/7.02  --inst_restr_to_given                   false
% 51.61/7.02  --inst_activity_threshold               500
% 51.61/7.02  --inst_out_proof                        true
% 51.61/7.02  
% 51.61/7.02  ------ Resolution Options
% 51.61/7.02  
% 51.61/7.02  --resolution_flag                       true
% 51.61/7.02  --res_lit_sel                           adaptive
% 51.61/7.02  --res_lit_sel_side                      none
% 51.61/7.02  --res_ordering                          kbo
% 51.61/7.02  --res_to_prop_solver                    active
% 51.61/7.02  --res_prop_simpl_new                    false
% 51.61/7.02  --res_prop_simpl_given                  true
% 51.61/7.02  --res_passive_queue_type                priority_queues
% 51.61/7.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.61/7.02  --res_passive_queues_freq               [15;5]
% 51.61/7.02  --res_forward_subs                      full
% 51.61/7.02  --res_backward_subs                     full
% 51.61/7.02  --res_forward_subs_resolution           true
% 51.61/7.02  --res_backward_subs_resolution          true
% 51.61/7.02  --res_orphan_elimination                true
% 51.61/7.02  --res_time_limit                        2.
% 51.61/7.02  --res_out_proof                         true
% 51.61/7.02  
% 51.61/7.02  ------ Superposition Options
% 51.61/7.02  
% 51.61/7.02  --superposition_flag                    true
% 51.61/7.02  --sup_passive_queue_type                priority_queues
% 51.61/7.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.61/7.02  --sup_passive_queues_freq               [8;1;4]
% 51.61/7.02  --demod_completeness_check              fast
% 51.61/7.02  --demod_use_ground                      true
% 51.61/7.02  --sup_to_prop_solver                    passive
% 51.61/7.02  --sup_prop_simpl_new                    true
% 51.61/7.02  --sup_prop_simpl_given                  true
% 51.61/7.02  --sup_fun_splitting                     true
% 51.61/7.02  --sup_smt_interval                      50000
% 51.61/7.02  
% 51.61/7.02  ------ Superposition Simplification Setup
% 51.61/7.02  
% 51.61/7.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.61/7.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.61/7.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.61/7.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.61/7.02  --sup_full_triv                         [TrivRules;PropSubs]
% 51.61/7.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.61/7.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.61/7.02  --sup_immed_triv                        [TrivRules]
% 51.61/7.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.61/7.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.61/7.02  --sup_immed_bw_main                     []
% 51.61/7.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.61/7.02  --sup_input_triv                        [Unflattening;TrivRules]
% 51.61/7.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.61/7.02  --sup_input_bw                          []
% 51.61/7.02  
% 51.61/7.02  ------ Combination Options
% 51.61/7.02  
% 51.61/7.02  --comb_res_mult                         3
% 51.61/7.02  --comb_sup_mult                         2
% 51.61/7.02  --comb_inst_mult                        10
% 51.61/7.02  
% 51.61/7.02  ------ Debug Options
% 51.61/7.02  
% 51.61/7.02  --dbg_backtrace                         false
% 51.61/7.02  --dbg_dump_prop_clauses                 false
% 51.61/7.02  --dbg_dump_prop_clauses_file            -
% 51.61/7.02  --dbg_out_stat                          false
% 51.61/7.02  ------ Parsing...
% 51.61/7.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.61/7.02  
% 51.61/7.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 51.61/7.02  
% 51.61/7.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.61/7.02  
% 51.61/7.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.61/7.02  ------ Proving...
% 51.61/7.02  ------ Problem Properties 
% 51.61/7.02  
% 51.61/7.02  
% 51.61/7.02  clauses                                 27
% 51.61/7.02  conjectures                             5
% 51.61/7.02  EPR                                     6
% 51.61/7.02  Horn                                    17
% 51.61/7.02  unary                                   6
% 51.61/7.02  binary                                  4
% 51.61/7.02  lits                                    89
% 51.61/7.02  lits eq                                 11
% 51.61/7.02  fd_pure                                 0
% 51.61/7.02  fd_pseudo                               0
% 51.61/7.02  fd_cond                                 0
% 51.61/7.02  fd_pseudo_cond                          2
% 51.61/7.02  AC symbols                              0
% 51.61/7.02  
% 51.61/7.02  ------ Schedule dynamic 5 is on 
% 51.61/7.02  
% 51.61/7.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.61/7.02  
% 51.61/7.02  
% 51.61/7.02  ------ 
% 51.61/7.02  Current options:
% 51.61/7.02  ------ 
% 51.61/7.02  
% 51.61/7.02  ------ Input Options
% 51.61/7.02  
% 51.61/7.02  --out_options                           all
% 51.61/7.02  --tptp_safe_out                         true
% 51.61/7.02  --problem_path                          ""
% 51.61/7.02  --include_path                          ""
% 51.61/7.02  --clausifier                            res/vclausify_rel
% 51.61/7.02  --clausifier_options                    ""
% 51.61/7.02  --stdin                                 false
% 51.61/7.02  --stats_out                             all
% 51.61/7.02  
% 51.61/7.02  ------ General Options
% 51.61/7.02  
% 51.61/7.02  --fof                                   false
% 51.61/7.02  --time_out_real                         305.
% 51.61/7.02  --time_out_virtual                      -1.
% 51.61/7.02  --symbol_type_check                     false
% 51.61/7.02  --clausify_out                          false
% 51.61/7.02  --sig_cnt_out                           false
% 51.61/7.02  --trig_cnt_out                          false
% 51.61/7.02  --trig_cnt_out_tolerance                1.
% 51.61/7.02  --trig_cnt_out_sk_spl                   false
% 51.61/7.02  --abstr_cl_out                          false
% 51.61/7.02  
% 51.61/7.02  ------ Global Options
% 51.61/7.02  
% 51.61/7.02  --schedule                              default
% 51.61/7.02  --add_important_lit                     false
% 51.61/7.02  --prop_solver_per_cl                    1000
% 51.61/7.02  --min_unsat_core                        false
% 51.61/7.02  --soft_assumptions                      false
% 51.61/7.02  --soft_lemma_size                       3
% 51.61/7.02  --prop_impl_unit_size                   0
% 51.61/7.02  --prop_impl_unit                        []
% 51.61/7.02  --share_sel_clauses                     true
% 51.61/7.02  --reset_solvers                         false
% 51.61/7.02  --bc_imp_inh                            [conj_cone]
% 51.61/7.02  --conj_cone_tolerance                   3.
% 51.61/7.02  --extra_neg_conj                        none
% 51.61/7.02  --large_theory_mode                     true
% 51.61/7.02  --prolific_symb_bound                   200
% 51.61/7.02  --lt_threshold                          2000
% 51.61/7.02  --clause_weak_htbl                      true
% 51.61/7.02  --gc_record_bc_elim                     false
% 51.61/7.02  
% 51.61/7.02  ------ Preprocessing Options
% 51.61/7.02  
% 51.61/7.02  --preprocessing_flag                    true
% 51.61/7.02  --time_out_prep_mult                    0.1
% 51.61/7.02  --splitting_mode                        input
% 51.61/7.02  --splitting_grd                         true
% 51.61/7.02  --splitting_cvd                         false
% 51.61/7.02  --splitting_cvd_svl                     false
% 51.61/7.02  --splitting_nvd                         32
% 51.61/7.02  --sub_typing                            true
% 51.61/7.02  --prep_gs_sim                           true
% 51.61/7.02  --prep_unflatten                        true
% 51.61/7.02  --prep_res_sim                          true
% 51.61/7.02  --prep_upred                            true
% 51.61/7.02  --prep_sem_filter                       exhaustive
% 51.61/7.02  --prep_sem_filter_out                   false
% 51.61/7.02  --pred_elim                             true
% 51.61/7.02  --res_sim_input                         true
% 51.61/7.02  --eq_ax_congr_red                       true
% 51.61/7.02  --pure_diseq_elim                       true
% 51.61/7.02  --brand_transform                       false
% 51.61/7.02  --non_eq_to_eq                          false
% 51.61/7.02  --prep_def_merge                        true
% 51.61/7.02  --prep_def_merge_prop_impl              false
% 51.61/7.02  --prep_def_merge_mbd                    true
% 51.61/7.02  --prep_def_merge_tr_red                 false
% 51.61/7.02  --prep_def_merge_tr_cl                  false
% 51.61/7.02  --smt_preprocessing                     true
% 51.61/7.02  --smt_ac_axioms                         fast
% 51.61/7.02  --preprocessed_out                      false
% 51.61/7.02  --preprocessed_stats                    false
% 51.61/7.02  
% 51.61/7.02  ------ Abstraction refinement Options
% 51.61/7.02  
% 51.61/7.02  --abstr_ref                             []
% 51.61/7.02  --abstr_ref_prep                        false
% 51.61/7.02  --abstr_ref_until_sat                   false
% 51.61/7.02  --abstr_ref_sig_restrict                funpre
% 51.61/7.02  --abstr_ref_af_restrict_to_split_sk     false
% 51.61/7.02  --abstr_ref_under                       []
% 51.61/7.02  
% 51.61/7.02  ------ SAT Options
% 51.61/7.02  
% 51.61/7.02  --sat_mode                              false
% 51.61/7.02  --sat_fm_restart_options                ""
% 51.61/7.02  --sat_gr_def                            false
% 51.61/7.02  --sat_epr_types                         true
% 51.61/7.02  --sat_non_cyclic_types                  false
% 51.61/7.02  --sat_finite_models                     false
% 51.61/7.02  --sat_fm_lemmas                         false
% 51.61/7.02  --sat_fm_prep                           false
% 51.61/7.02  --sat_fm_uc_incr                        true
% 51.61/7.02  --sat_out_model                         small
% 51.61/7.02  --sat_out_clauses                       false
% 51.61/7.02  
% 51.61/7.02  ------ QBF Options
% 51.61/7.02  
% 51.61/7.02  --qbf_mode                              false
% 51.61/7.02  --qbf_elim_univ                         false
% 51.61/7.02  --qbf_dom_inst                          none
% 51.61/7.02  --qbf_dom_pre_inst                      false
% 51.61/7.02  --qbf_sk_in                             false
% 51.61/7.02  --qbf_pred_elim                         true
% 51.61/7.02  --qbf_split                             512
% 51.61/7.02  
% 51.61/7.02  ------ BMC1 Options
% 51.61/7.02  
% 51.61/7.02  --bmc1_incremental                      false
% 51.61/7.02  --bmc1_axioms                           reachable_all
% 51.61/7.02  --bmc1_min_bound                        0
% 51.61/7.02  --bmc1_max_bound                        -1
% 51.61/7.02  --bmc1_max_bound_default                -1
% 51.61/7.02  --bmc1_symbol_reachability              true
% 51.61/7.02  --bmc1_property_lemmas                  false
% 51.61/7.02  --bmc1_k_induction                      false
% 51.61/7.02  --bmc1_non_equiv_states                 false
% 51.61/7.02  --bmc1_deadlock                         false
% 51.61/7.02  --bmc1_ucm                              false
% 51.61/7.02  --bmc1_add_unsat_core                   none
% 51.61/7.02  --bmc1_unsat_core_children              false
% 51.61/7.02  --bmc1_unsat_core_extrapolate_axioms    false
% 51.61/7.02  --bmc1_out_stat                         full
% 51.61/7.02  --bmc1_ground_init                      false
% 51.61/7.02  --bmc1_pre_inst_next_state              false
% 51.61/7.02  --bmc1_pre_inst_state                   false
% 51.61/7.02  --bmc1_pre_inst_reach_state             false
% 51.61/7.02  --bmc1_out_unsat_core                   false
% 51.61/7.02  --bmc1_aig_witness_out                  false
% 51.61/7.02  --bmc1_verbose                          false
% 51.61/7.02  --bmc1_dump_clauses_tptp                false
% 51.61/7.02  --bmc1_dump_unsat_core_tptp             false
% 51.61/7.02  --bmc1_dump_file                        -
% 51.61/7.02  --bmc1_ucm_expand_uc_limit              128
% 51.61/7.02  --bmc1_ucm_n_expand_iterations          6
% 51.61/7.02  --bmc1_ucm_extend_mode                  1
% 51.61/7.02  --bmc1_ucm_init_mode                    2
% 51.61/7.02  --bmc1_ucm_cone_mode                    none
% 51.61/7.02  --bmc1_ucm_reduced_relation_type        0
% 51.61/7.02  --bmc1_ucm_relax_model                  4
% 51.61/7.02  --bmc1_ucm_full_tr_after_sat            true
% 51.61/7.02  --bmc1_ucm_expand_neg_assumptions       false
% 51.61/7.02  --bmc1_ucm_layered_model                none
% 51.61/7.02  --bmc1_ucm_max_lemma_size               10
% 51.61/7.02  
% 51.61/7.02  ------ AIG Options
% 51.61/7.02  
% 51.61/7.02  --aig_mode                              false
% 51.61/7.02  
% 51.61/7.02  ------ Instantiation Options
% 51.61/7.02  
% 51.61/7.02  --instantiation_flag                    true
% 51.61/7.02  --inst_sos_flag                         true
% 51.61/7.02  --inst_sos_phase                        true
% 51.61/7.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.61/7.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.61/7.02  --inst_lit_sel_side                     none
% 51.61/7.02  --inst_solver_per_active                1400
% 51.61/7.02  --inst_solver_calls_frac                1.
% 51.61/7.02  --inst_passive_queue_type               priority_queues
% 51.61/7.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.61/7.02  --inst_passive_queues_freq              [25;2]
% 51.61/7.02  --inst_dismatching                      true
% 51.61/7.02  --inst_eager_unprocessed_to_passive     true
% 51.61/7.02  --inst_prop_sim_given                   true
% 51.61/7.02  --inst_prop_sim_new                     false
% 51.61/7.02  --inst_subs_new                         false
% 51.61/7.02  --inst_eq_res_simp                      false
% 51.61/7.02  --inst_subs_given                       false
% 51.61/7.02  --inst_orphan_elimination               true
% 51.61/7.02  --inst_learning_loop_flag               true
% 51.61/7.02  --inst_learning_start                   3000
% 51.61/7.02  --inst_learning_factor                  2
% 51.61/7.02  --inst_start_prop_sim_after_learn       3
% 51.61/7.02  --inst_sel_renew                        solver
% 51.61/7.02  --inst_lit_activity_flag                true
% 51.61/7.02  --inst_restr_to_given                   false
% 51.61/7.02  --inst_activity_threshold               500
% 51.61/7.02  --inst_out_proof                        true
% 51.61/7.02  
% 51.61/7.02  ------ Resolution Options
% 51.61/7.02  
% 51.61/7.02  --resolution_flag                       false
% 51.61/7.02  --res_lit_sel                           adaptive
% 51.61/7.02  --res_lit_sel_side                      none
% 51.61/7.02  --res_ordering                          kbo
% 51.61/7.02  --res_to_prop_solver                    active
% 51.61/7.02  --res_prop_simpl_new                    false
% 51.61/7.02  --res_prop_simpl_given                  true
% 51.61/7.02  --res_passive_queue_type                priority_queues
% 51.61/7.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.61/7.02  --res_passive_queues_freq               [15;5]
% 51.61/7.02  --res_forward_subs                      full
% 51.61/7.02  --res_backward_subs                     full
% 51.61/7.02  --res_forward_subs_resolution           true
% 51.61/7.02  --res_backward_subs_resolution          true
% 51.61/7.02  --res_orphan_elimination                true
% 51.61/7.02  --res_time_limit                        2.
% 51.61/7.02  --res_out_proof                         true
% 51.61/7.02  
% 51.61/7.02  ------ Superposition Options
% 51.61/7.02  
% 51.61/7.02  --superposition_flag                    true
% 51.61/7.02  --sup_passive_queue_type                priority_queues
% 51.61/7.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.61/7.02  --sup_passive_queues_freq               [8;1;4]
% 51.61/7.02  --demod_completeness_check              fast
% 51.61/7.02  --demod_use_ground                      true
% 51.61/7.02  --sup_to_prop_solver                    passive
% 51.61/7.02  --sup_prop_simpl_new                    true
% 51.61/7.02  --sup_prop_simpl_given                  true
% 51.61/7.02  --sup_fun_splitting                     true
% 51.61/7.02  --sup_smt_interval                      50000
% 51.61/7.02  
% 51.61/7.02  ------ Superposition Simplification Setup
% 51.61/7.02  
% 51.61/7.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.61/7.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.61/7.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.61/7.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.61/7.02  --sup_full_triv                         [TrivRules;PropSubs]
% 51.61/7.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.61/7.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.61/7.02  --sup_immed_triv                        [TrivRules]
% 51.61/7.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.61/7.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.61/7.02  --sup_immed_bw_main                     []
% 51.61/7.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.61/7.02  --sup_input_triv                        [Unflattening;TrivRules]
% 51.61/7.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.61/7.02  --sup_input_bw                          []
% 51.61/7.02  
% 51.61/7.02  ------ Combination Options
% 51.61/7.02  
% 51.61/7.02  --comb_res_mult                         3
% 51.61/7.02  --comb_sup_mult                         2
% 51.61/7.02  --comb_inst_mult                        10
% 51.61/7.02  
% 51.61/7.02  ------ Debug Options
% 51.61/7.02  
% 51.61/7.02  --dbg_backtrace                         false
% 51.61/7.02  --dbg_dump_prop_clauses                 false
% 51.61/7.02  --dbg_dump_prop_clauses_file            -
% 51.61/7.02  --dbg_out_stat                          false
% 51.61/7.02  
% 51.61/7.02  
% 51.61/7.02  
% 51.61/7.02  
% 51.61/7.02  ------ Proving...
% 51.61/7.02  
% 51.61/7.02  
% 51.61/7.02  % SZS status Theorem for theBenchmark.p
% 51.61/7.02  
% 51.61/7.02  % SZS output start CNFRefutation for theBenchmark.p
% 51.61/7.02  
% 51.61/7.02  fof(f5,axiom,(
% 51.61/7.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X2)) & l1_waybel_0(X2,X1) & ~v2_struct_0(X2) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))))),
% 51.61/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.61/7.02  
% 51.61/7.02  fof(f13,plain,(
% 51.61/7.02    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | (~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)))),
% 51.61/7.02    inference(ennf_transformation,[],[f5])).
% 51.61/7.02  
% 51.61/7.02  fof(f14,plain,(
% 51.61/7.02    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 51.61/7.02    inference(flattening,[],[f13])).
% 51.61/7.02  
% 51.61/7.02  fof(f35,plain,(
% 51.61/7.02    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 51.61/7.02    inference(nnf_transformation,[],[f14])).
% 51.61/7.02  
% 51.61/7.02  fof(f36,plain,(
% 51.61/7.02    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 51.61/7.02    inference(rectify,[],[f35])).
% 51.61/7.02  
% 51.61/7.02  fof(f37,plain,(
% 51.61/7.02    ! [X3,X2,X0] : (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) => (r1_orders_2(X2,X3,sK6(X0,X2,X3)) & sK6(X0,X2,X3) = X0 & m1_subset_1(sK6(X0,X2,X3),u1_struct_0(X2))))),
% 51.61/7.02    introduced(choice_axiom,[])).
% 51.61/7.02  
% 51.61/7.02  fof(f38,plain,(
% 51.61/7.02    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & ((r1_orders_2(X2,X3,sK6(X0,X2,X3)) & sK6(X0,X2,X3) = X0 & m1_subset_1(sK6(X0,X2,X3),u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 51.61/7.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 51.61/7.02  
% 51.61/7.02  fof(f67,plain,(
% 51.61/7.02    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f38])).
% 51.61/7.02  
% 51.61/7.02  fof(f79,plain,(
% 51.61/7.02    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,a_3_0_waybel_9(X1,X2,X3)) | ~r1_orders_2(X2,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 51.61/7.02    inference(equality_resolution,[],[f67])).
% 51.61/7.02  
% 51.61/7.02  fof(f6,conjecture,(
% 51.61/7.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2))))),
% 51.61/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.61/7.02  
% 51.61/7.02  fof(f7,negated_conjecture,(
% 51.61/7.02    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2))))),
% 51.61/7.02    inference(negated_conjecture,[],[f6])).
% 51.61/7.02  
% 51.61/7.02  fof(f15,plain,(
% 51.61/7.02    ? [X0] : (? [X1] : (? [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 51.61/7.02    inference(ennf_transformation,[],[f7])).
% 51.61/7.02  
% 51.61/7.02  fof(f16,plain,(
% 51.61/7.02    ? [X0] : (? [X1] : (? [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 51.61/7.02    inference(flattening,[],[f15])).
% 51.61/7.02  
% 51.61/7.02  fof(f41,plain,(
% 51.61/7.02    ( ! [X0,X1] : (? [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X1))) => (u1_struct_0(k4_waybel_9(X0,X1,sK9)) != a_3_0_waybel_9(X0,X1,sK9) & m1_subset_1(sK9,u1_struct_0(X1)))) )),
% 51.61/7.02    introduced(choice_axiom,[])).
% 51.61/7.02  
% 51.61/7.02  fof(f40,plain,(
% 51.61/7.02    ( ! [X0] : (? [X1] : (? [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (u1_struct_0(k4_waybel_9(X0,sK8,X2)) != a_3_0_waybel_9(X0,sK8,X2) & m1_subset_1(X2,u1_struct_0(sK8))) & l1_waybel_0(sK8,X0) & ~v2_struct_0(sK8))) )),
% 51.61/7.02    introduced(choice_axiom,[])).
% 51.61/7.02  
% 51.61/7.02  fof(f39,plain,(
% 51.61/7.02    ? [X0] : (? [X1] : (? [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (u1_struct_0(k4_waybel_9(sK7,X1,X2)) != a_3_0_waybel_9(sK7,X1,X2) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK7) & ~v2_struct_0(X1)) & l1_struct_0(sK7) & ~v2_struct_0(sK7))),
% 51.61/7.02    introduced(choice_axiom,[])).
% 51.61/7.02  
% 51.61/7.02  fof(f42,plain,(
% 51.61/7.02    ((u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != a_3_0_waybel_9(sK7,sK8,sK9) & m1_subset_1(sK9,u1_struct_0(sK8))) & l1_waybel_0(sK8,sK7) & ~v2_struct_0(sK8)) & l1_struct_0(sK7) & ~v2_struct_0(sK7)),
% 51.61/7.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f16,f41,f40,f39])).
% 51.61/7.02  
% 51.61/7.02  fof(f69,plain,(
% 51.61/7.02    l1_struct_0(sK7)),
% 51.61/7.02    inference(cnf_transformation,[],[f42])).
% 51.61/7.02  
% 51.61/7.02  fof(f68,plain,(
% 51.61/7.02    ~v2_struct_0(sK7)),
% 51.61/7.02    inference(cnf_transformation,[],[f42])).
% 51.61/7.02  
% 51.61/7.02  fof(f1,axiom,(
% 51.61/7.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 51.61/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.61/7.02  
% 51.61/7.02  fof(f8,plain,(
% 51.61/7.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 51.61/7.02    inference(ennf_transformation,[],[f1])).
% 51.61/7.02  
% 51.61/7.02  fof(f20,plain,(
% 51.61/7.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 51.61/7.02    inference(nnf_transformation,[],[f8])).
% 51.61/7.02  
% 51.61/7.02  fof(f21,plain,(
% 51.61/7.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.61/7.02    inference(rectify,[],[f20])).
% 51.61/7.02  
% 51.61/7.02  fof(f22,plain,(
% 51.61/7.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 51.61/7.02    introduced(choice_axiom,[])).
% 51.61/7.02  
% 51.61/7.02  fof(f23,plain,(
% 51.61/7.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.61/7.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 51.61/7.02  
% 51.61/7.02  fof(f44,plain,(
% 51.61/7.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f23])).
% 51.61/7.02  
% 51.61/7.02  fof(f72,plain,(
% 51.61/7.02    m1_subset_1(sK9,u1_struct_0(sK8))),
% 51.61/7.02    inference(cnf_transformation,[],[f42])).
% 51.61/7.02  
% 51.61/7.02  fof(f3,axiom,(
% 51.61/7.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))))))),
% 51.61/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.61/7.02  
% 51.61/7.02  fof(f9,plain,(
% 51.61/7.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 51.61/7.02    inference(ennf_transformation,[],[f3])).
% 51.61/7.02  
% 51.61/7.02  fof(f10,plain,(
% 51.61/7.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 51.61/7.02    inference(flattening,[],[f9])).
% 51.61/7.02  
% 51.61/7.02  fof(f18,plain,(
% 51.61/7.02    ! [X2,X0,X1,X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> sP0(X3,X1,X0,X2)) | ~sP1(X2,X0,X1,X3))),
% 51.61/7.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 51.61/7.02  
% 51.61/7.02  fof(f17,plain,(
% 51.61/7.02    ! [X3,X1,X0,X2] : (sP0(X3,X1,X0,X2) <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))),
% 51.61/7.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 51.61/7.02  
% 51.61/7.02  fof(f19,plain,(
% 51.61/7.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP1(X2,X0,X1,X3) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 51.61/7.02    inference(definition_folding,[],[f10,f18,f17])).
% 51.61/7.02  
% 51.61/7.02  fof(f61,plain,(
% 51.61/7.02    ( ! [X2,X0,X3,X1] : (sP1(X2,X0,X1,X3) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f19])).
% 51.61/7.02  
% 51.61/7.02  fof(f4,axiom,(
% 51.61/7.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 51.61/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.61/7.02  
% 51.61/7.02  fof(f11,plain,(
% 51.61/7.02    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 51.61/7.02    inference(ennf_transformation,[],[f4])).
% 51.61/7.02  
% 51.61/7.02  fof(f12,plain,(
% 51.61/7.02    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 51.61/7.02    inference(flattening,[],[f11])).
% 51.61/7.02  
% 51.61/7.02  fof(f62,plain,(
% 51.61/7.02    ( ! [X2,X0,X1] : (v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f12])).
% 51.61/7.02  
% 51.61/7.02  fof(f63,plain,(
% 51.61/7.02    ( ! [X2,X0,X1] : (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f12])).
% 51.61/7.02  
% 51.61/7.02  fof(f26,plain,(
% 51.61/7.02    ! [X2,X0,X1,X3] : (((k4_waybel_9(X0,X1,X2) = X3 | ~sP0(X3,X1,X0,X2)) & (sP0(X3,X1,X0,X2) | k4_waybel_9(X0,X1,X2) != X3)) | ~sP1(X2,X0,X1,X3))),
% 51.61/7.02    inference(nnf_transformation,[],[f18])).
% 51.61/7.02  
% 51.61/7.02  fof(f27,plain,(
% 51.61/7.02    ! [X0,X1,X2,X3] : (((k4_waybel_9(X1,X2,X0) = X3 | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | k4_waybel_9(X1,X2,X0) != X3)) | ~sP1(X0,X1,X2,X3))),
% 51.61/7.02    inference(rectify,[],[f26])).
% 51.61/7.02  
% 51.61/7.02  fof(f49,plain,(
% 51.61/7.02    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0) | k4_waybel_9(X1,X2,X0) != X3 | ~sP1(X0,X1,X2,X3)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f27])).
% 51.61/7.02  
% 51.61/7.02  fof(f76,plain,(
% 51.61/7.02    ( ! [X2,X0,X1] : (sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) | ~sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))) )),
% 51.61/7.02    inference(equality_resolution,[],[f49])).
% 51.61/7.02  
% 51.61/7.02  fof(f28,plain,(
% 51.61/7.02    ! [X3,X1,X0,X2] : ((sP0(X3,X1,X0,X2) | (u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3)))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))))) | ~sP0(X3,X1,X0,X2)))),
% 51.61/7.02    inference(nnf_transformation,[],[f17])).
% 51.61/7.02  
% 51.61/7.02  fof(f29,plain,(
% 51.61/7.02    ! [X3,X1,X0,X2] : ((sP0(X3,X1,X0,X2) | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))))) | ~sP0(X3,X1,X0,X2)))),
% 51.61/7.02    inference(flattening,[],[f28])).
% 51.61/7.02  
% 51.61/7.02  fof(f30,plain,(
% 51.61/7.02    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) | ~r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X3,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X0))) & (? [X6] : (r1_orders_2(X1,X3,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X0))))) & ((u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) & ! [X7] : ((r2_hidden(X7,u1_struct_0(X0)) | ! [X8] : (~r1_orders_2(X1,X3,X8) | X7 != X8 | ~m1_subset_1(X8,u1_struct_0(X1)))) & (? [X9] : (r1_orders_2(X1,X3,X9) & X7 = X9 & m1_subset_1(X9,u1_struct_0(X1))) | ~r2_hidden(X7,u1_struct_0(X0))))) | ~sP0(X0,X1,X2,X3)))),
% 51.61/7.02    inference(rectify,[],[f29])).
% 51.61/7.02  
% 51.61/7.02  fof(f33,plain,(
% 51.61/7.02    ! [X7,X3,X1] : (? [X9] : (r1_orders_2(X1,X3,X9) & X7 = X9 & m1_subset_1(X9,u1_struct_0(X1))) => (r1_orders_2(X1,X3,sK5(X1,X3,X7)) & sK5(X1,X3,X7) = X7 & m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1))))),
% 51.61/7.02    introduced(choice_axiom,[])).
% 51.61/7.02  
% 51.61/7.02  fof(f32,plain,(
% 51.61/7.02    ( ! [X4] : (! [X3,X1,X0] : (? [X6] : (r1_orders_2(X1,X3,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) => (r1_orders_2(X1,X3,sK4(X0,X1,X3)) & sK4(X0,X1,X3) = X4 & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X1))))) )),
% 51.61/7.02    introduced(choice_axiom,[])).
% 51.61/7.02  
% 51.61/7.02  fof(f31,plain,(
% 51.61/7.02    ! [X3,X1,X0] : (? [X4] : ((! [X5] : (~r1_orders_2(X1,X3,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X0))) & (? [X6] : (r1_orders_2(X1,X3,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X0)))) => ((! [X5] : (~r1_orders_2(X1,X3,X5) | sK3(X0,X1,X3) != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0))) & (? [X6] : (r1_orders_2(X1,X3,X6) & sK3(X0,X1,X3) = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0)))))),
% 51.61/7.02    introduced(choice_axiom,[])).
% 51.61/7.02  
% 51.61/7.02  fof(f34,plain,(
% 51.61/7.02    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) | ~r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) | ((! [X5] : (~r1_orders_2(X1,X3,X5) | sK3(X0,X1,X3) != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0))) & ((r1_orders_2(X1,X3,sK4(X0,X1,X3)) & sK3(X0,X1,X3) = sK4(X0,X1,X3) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X1))) | r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0))))) & ((u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) & ! [X7] : ((r2_hidden(X7,u1_struct_0(X0)) | ! [X8] : (~r1_orders_2(X1,X3,X8) | X7 != X8 | ~m1_subset_1(X8,u1_struct_0(X1)))) & ((r1_orders_2(X1,X3,sK5(X1,X3,X7)) & sK5(X1,X3,X7) = X7 & m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1))) | ~r2_hidden(X7,u1_struct_0(X0))))) | ~sP0(X0,X1,X2,X3)))),
% 51.61/7.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 51.61/7.02  
% 51.61/7.02  fof(f52,plain,(
% 51.61/7.02    ( ! [X2,X0,X7,X3,X1] : (sK5(X1,X3,X7) = X7 | ~r2_hidden(X7,u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f34])).
% 51.61/7.02  
% 51.61/7.02  fof(f65,plain,(
% 51.61/7.02    ( ! [X2,X0,X3,X1] : (sK6(X0,X2,X3) = X0 | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f38])).
% 51.61/7.02  
% 51.61/7.02  fof(f2,axiom,(
% 51.61/7.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.61/7.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.61/7.02  
% 51.61/7.02  fof(f24,plain,(
% 51.61/7.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.61/7.02    inference(nnf_transformation,[],[f2])).
% 51.61/7.02  
% 51.61/7.02  fof(f25,plain,(
% 51.61/7.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.61/7.02    inference(flattening,[],[f24])).
% 51.61/7.02  
% 51.61/7.02  fof(f48,plain,(
% 51.61/7.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f25])).
% 51.61/7.02  
% 51.61/7.02  fof(f70,plain,(
% 51.61/7.02    ~v2_struct_0(sK8)),
% 51.61/7.02    inference(cnf_transformation,[],[f42])).
% 51.61/7.02  
% 51.61/7.02  fof(f71,plain,(
% 51.61/7.02    l1_waybel_0(sK8,sK7)),
% 51.61/7.02    inference(cnf_transformation,[],[f42])).
% 51.61/7.02  
% 51.61/7.02  fof(f73,plain,(
% 51.61/7.02    u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != a_3_0_waybel_9(sK7,sK8,sK9)),
% 51.61/7.02    inference(cnf_transformation,[],[f42])).
% 51.61/7.02  
% 51.61/7.02  fof(f43,plain,(
% 51.61/7.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f23])).
% 51.61/7.02  
% 51.61/7.02  fof(f64,plain,(
% 51.61/7.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X2,X3),u1_struct_0(X2)) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f38])).
% 51.61/7.02  
% 51.61/7.02  fof(f66,plain,(
% 51.61/7.02    ( ! [X2,X0,X3,X1] : (r1_orders_2(X2,X3,sK6(X0,X2,X3)) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f38])).
% 51.61/7.02  
% 51.61/7.02  fof(f54,plain,(
% 51.61/7.02    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,u1_struct_0(X0)) | ~r1_orders_2(X1,X3,X8) | X7 != X8 | ~m1_subset_1(X8,u1_struct_0(X1)) | ~sP0(X0,X1,X2,X3)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f34])).
% 51.61/7.02  
% 51.61/7.02  fof(f78,plain,(
% 51.61/7.02    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,u1_struct_0(X0)) | ~r1_orders_2(X1,X3,X8) | ~m1_subset_1(X8,u1_struct_0(X1)) | ~sP0(X0,X1,X2,X3)) )),
% 51.61/7.02    inference(equality_resolution,[],[f54])).
% 51.61/7.02  
% 51.61/7.02  fof(f45,plain,(
% 51.61/7.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f23])).
% 51.61/7.02  
% 51.61/7.02  fof(f53,plain,(
% 51.61/7.02    ( ! [X2,X0,X7,X3,X1] : (r1_orders_2(X1,X3,sK5(X1,X3,X7)) | ~r2_hidden(X7,u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f34])).
% 51.61/7.02  
% 51.61/7.02  fof(f51,plain,(
% 51.61/7.02    ( ! [X2,X0,X7,X3,X1] : (m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1)) | ~r2_hidden(X7,u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3)) )),
% 51.61/7.02    inference(cnf_transformation,[],[f34])).
% 51.61/7.02  
% 51.61/7.02  fof(f46,plain,(
% 51.61/7.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.61/7.02    inference(cnf_transformation,[],[f25])).
% 51.61/7.02  
% 51.61/7.02  fof(f75,plain,(
% 51.61/7.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.61/7.02    inference(equality_resolution,[],[f46])).
% 51.61/7.02  
% 51.61/7.02  cnf(c_21,plain,
% 51.61/7.02      ( ~ r1_orders_2(X0,X1,X2)
% 51.61/7.02      | ~ l1_waybel_0(X0,X3)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
% 51.61/7.02      | ~ l1_struct_0(X3)
% 51.61/7.02      | v2_struct_0(X3)
% 51.61/7.02      | v2_struct_0(X0) ),
% 51.61/7.02      inference(cnf_transformation,[],[f79]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_29,negated_conjecture,
% 51.61/7.02      ( l1_struct_0(sK7) ),
% 51.61/7.02      inference(cnf_transformation,[],[f69]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_700,plain,
% 51.61/7.02      ( ~ r1_orders_2(X0,X1,X2)
% 51.61/7.02      | ~ l1_waybel_0(X0,X3)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | v2_struct_0(X3)
% 51.61/7.02      | sK7 != X3 ),
% 51.61/7.02      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_701,plain,
% 51.61/7.02      ( ~ r1_orders_2(X0,X1,X2)
% 51.61/7.02      | ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | v2_struct_0(sK7) ),
% 51.61/7.02      inference(unflattening,[status(thm)],[c_700]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_30,negated_conjecture,
% 51.61/7.02      ( ~ v2_struct_0(sK7) ),
% 51.61/7.02      inference(cnf_transformation,[],[f68]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_705,plain,
% 51.61/7.02      ( v2_struct_0(X0)
% 51.61/7.02      | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | ~ r1_orders_2(X0,X1,X2) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_701,c_30]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_706,plain,
% 51.61/7.02      ( ~ r1_orders_2(X0,X1,X2)
% 51.61/7.02      | ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | v2_struct_0(X0) ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_705]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_77434,plain,
% 51.61/7.02      ( ~ r1_orders_2(sK8,X0,X1)
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 51.61/7.02      | r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_706]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_77641,plain,
% 51.61/7.02      ( ~ r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_77434]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_77642,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_77641]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2193,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,X2) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1)) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_1,plain,
% 51.61/7.02      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 51.61/7.02      inference(cnf_transformation,[],[f44]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2217,plain,
% 51.61/7.02      ( r2_hidden(sK2(X0,X1),X0) = iProver_top
% 51.61/7.02      | r1_tarski(X0,X1) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_26,negated_conjecture,
% 51.61/7.02      ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
% 51.61/7.02      inference(cnf_transformation,[],[f72]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2206,plain,
% 51.61/7.02      ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_18,plain,
% 51.61/7.02      ( sP1(X0,X1,X2,X3)
% 51.61/7.02      | ~ v6_waybel_0(X3,X1)
% 51.61/7.02      | ~ l1_waybel_0(X3,X1)
% 51.61/7.02      | ~ l1_waybel_0(X2,X1)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 51.61/7.02      | ~ l1_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X2) ),
% 51.61/7.02      inference(cnf_transformation,[],[f61]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_20,plain,
% 51.61/7.02      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
% 51.61/7.02      | ~ l1_waybel_0(X1,X0)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 51.61/7.02      | ~ l1_struct_0(X0)
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | v2_struct_0(X1) ),
% 51.61/7.02      inference(cnf_transformation,[],[f62]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_332,plain,
% 51.61/7.02      ( sP1(X0,X1,X2,X3)
% 51.61/7.02      | ~ l1_waybel_0(X3,X1)
% 51.61/7.02      | ~ l1_waybel_0(X2,X1)
% 51.61/7.02      | ~ l1_waybel_0(X4,X5)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 51.61/7.02      | ~ m1_subset_1(X6,u1_struct_0(X4))
% 51.61/7.02      | ~ l1_struct_0(X1)
% 51.61/7.02      | ~ l1_struct_0(X5)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X2)
% 51.61/7.02      | v2_struct_0(X5)
% 51.61/7.02      | v2_struct_0(X4)
% 51.61/7.02      | X5 != X1
% 51.61/7.02      | k4_waybel_9(X5,X4,X6) != X3 ),
% 51.61/7.02      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_333,plain,
% 51.61/7.02      ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
% 51.61/7.02      | ~ l1_waybel_0(X2,X1)
% 51.61/7.02      | ~ l1_waybel_0(X3,X1)
% 51.61/7.02      | ~ l1_waybel_0(k4_waybel_9(X1,X3,X4),X1)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 51.61/7.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 51.61/7.02      | ~ l1_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X2)
% 51.61/7.02      | v2_struct_0(X3) ),
% 51.61/7.02      inference(unflattening,[status(thm)],[c_332]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_19,plain,
% 51.61/7.02      ( ~ l1_waybel_0(X0,X1)
% 51.61/7.02      | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | ~ l1_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X0) ),
% 51.61/7.02      inference(cnf_transformation,[],[f63]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_357,plain,
% 51.61/7.02      ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
% 51.61/7.02      | ~ l1_waybel_0(X3,X1)
% 51.61/7.02      | ~ l1_waybel_0(X2,X1)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 51.61/7.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 51.61/7.02      | ~ l1_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X2)
% 51.61/7.02      | v2_struct_0(X3) ),
% 51.61/7.02      inference(forward_subsumption_resolution,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_333,c_19]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_572,plain,
% 51.61/7.02      ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
% 51.61/7.02      | ~ l1_waybel_0(X3,X1)
% 51.61/7.02      | ~ l1_waybel_0(X2,X1)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 51.61/7.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X2)
% 51.61/7.02      | v2_struct_0(X3)
% 51.61/7.02      | sK7 != X1 ),
% 51.61/7.02      inference(resolution_lifted,[status(thm)],[c_357,c_29]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_573,plain,
% 51.61/7.02      ( sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3))
% 51.61/7.02      | ~ l1_waybel_0(X1,sK7)
% 51.61/7.02      | ~ l1_waybel_0(X2,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 51.61/7.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X2)
% 51.61/7.02      | v2_struct_0(sK7) ),
% 51.61/7.02      inference(unflattening,[status(thm)],[c_572]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_577,plain,
% 51.61/7.02      ( v2_struct_0(X2)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 51.61/7.02      | ~ l1_waybel_0(X2,sK7)
% 51.61/7.02      | ~ l1_waybel_0(X1,sK7)
% 51.61/7.02      | sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3)) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_573,c_30]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_578,plain,
% 51.61/7.02      ( sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3))
% 51.61/7.02      | ~ l1_waybel_0(X2,sK7)
% 51.61/7.02      | ~ l1_waybel_0(X1,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 51.61/7.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X2) ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_577]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2198,plain,
% 51.61/7.02      ( sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3)) = iProver_top
% 51.61/7.02      | l1_waybel_0(X1,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(X2,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 51.61/7.02      | v2_struct_0(X1) = iProver_top
% 51.61/7.02      | v2_struct_0(X2) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_7,plain,
% 51.61/7.02      ( ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))
% 51.61/7.02      | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) ),
% 51.61/7.02      inference(cnf_transformation,[],[f76]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2212,plain,
% 51.61/7.02      ( sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0)) != iProver_top
% 51.61/7.02      | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3153,plain,
% 51.61/7.02      ( sP0(k4_waybel_9(sK7,X0,X1),X0,sK7,X1) = iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2198,c_2212]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_16,plain,
% 51.61/7.02      ( ~ sP0(X0,X1,X2,X3)
% 51.61/7.02      | ~ r2_hidden(X4,u1_struct_0(X0))
% 51.61/7.02      | sK5(X1,X3,X4) = X4 ),
% 51.61/7.02      inference(cnf_transformation,[],[f52]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2208,plain,
% 51.61/7.02      ( sK5(X0,X1,X2) = X2
% 51.61/7.02      | sP0(X3,X0,X4,X1) != iProver_top
% 51.61/7.02      | r2_hidden(X2,u1_struct_0(X3)) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3251,plain,
% 51.61/7.02      ( sK5(X0,X1,X2) = X2
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_3153,c_2208]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4420,plain,
% 51.61/7.02      ( sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2217,c_3251]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_23,plain,
% 51.61/7.02      ( ~ l1_waybel_0(X0,X1)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
% 51.61/7.02      | ~ l1_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | sK6(X3,X0,X2) = X3 ),
% 51.61/7.02      inference(cnf_transformation,[],[f65]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_628,plain,
% 51.61/7.02      ( ~ l1_waybel_0(X0,X1)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | sK6(X3,X0,X2) = X3
% 51.61/7.02      | sK7 != X1 ),
% 51.61/7.02      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_629,plain,
% 51.61/7.02      ( ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | v2_struct_0(sK7)
% 51.61/7.02      | sK6(X2,X0,X1) = X2 ),
% 51.61/7.02      inference(unflattening,[status(thm)],[c_628]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_633,plain,
% 51.61/7.02      ( v2_struct_0(X0)
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | sK6(X2,X0,X1) = X2 ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_629,c_30]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_634,plain,
% 51.61/7.02      ( ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | sK6(X2,X0,X1) = X2 ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_633]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2196,plain,
% 51.61/7.02      ( sK6(X0,X1,X2) = X0
% 51.61/7.02      | l1_waybel_0(X1,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | r2_hidden(X0,a_3_0_waybel_9(sK7,X1,X2)) != iProver_top
% 51.61/7.02      | v2_struct_0(X1) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2673,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2217,c_2196]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3,plain,
% 51.61/7.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 51.61/7.02      inference(cnf_transformation,[],[f48]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2215,plain,
% 51.61/7.02      ( X0 = X1
% 51.61/7.02      | r1_tarski(X1,X0) != iProver_top
% 51.61/7.02      | r1_tarski(X0,X1) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2893,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | a_3_0_waybel_9(sK7,X0,X1) = X2
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(X2,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2673,c_2215]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_5353,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3))),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3)))
% 51.61/7.02      | sK5(X2,X3,sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))) = sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X2,X3)) = a_3_0_waybel_9(sK7,X0,X1)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(X2,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_4420,c_2893]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_70682,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_5353]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_28,negated_conjecture,
% 51.61/7.02      ( ~ v2_struct_0(sK8) ),
% 51.61/7.02      inference(cnf_transformation,[],[f70]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_33,plain,
% 51.61/7.02      ( v2_struct_0(sK8) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_27,negated_conjecture,
% 51.61/7.02      ( l1_waybel_0(sK8,sK7) ),
% 51.61/7.02      inference(cnf_transformation,[],[f71]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_34,plain,
% 51.61/7.02      ( l1_waybel_0(sK8,sK7) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_70725,plain,
% 51.61/7.02      ( v2_struct_0(X0) = iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_70682,c_33,c_34]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_70726,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_70725]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_70731,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_70726]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_25,negated_conjecture,
% 51.61/7.02      ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != a_3_0_waybel_9(sK7,sK8,sK9) ),
% 51.61/7.02      inference(cnf_transformation,[],[f73]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_70742,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | v2_struct_0(sK8)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
% 51.61/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_70731]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_70818,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_70731,c_28,c_27,c_25,c_70742]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_70819,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_70818]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2,plain,
% 51.61/7.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 51.61/7.02      inference(cnf_transformation,[],[f43]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2216,plain,
% 51.61/7.02      ( r2_hidden(X0,X1) != iProver_top
% 51.61/7.02      | r2_hidden(X0,X2) = iProver_top
% 51.61/7.02      | r1_tarski(X1,X2) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3146,plain,
% 51.61/7.02      ( r2_hidden(sK2(X0,X1),X2) = iProver_top
% 51.61/7.02      | r1_tarski(X0,X2) != iProver_top
% 51.61/7.02      | r1_tarski(X0,X1) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2217,c_2216]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4300,plain,
% 51.61/7.02      ( sK6(sK2(X0,X1),X2,X3) = sK2(X0,X1)
% 51.61/7.02      | l1_waybel_0(X2,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 51.61/7.02      | r1_tarski(X0,X1) = iProver_top
% 51.61/7.02      | r1_tarski(X0,a_3_0_waybel_9(sK7,X2,X3)) != iProver_top
% 51.61/7.02      | v2_struct_0(X2) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_3146,c_2196]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4428,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X3,X4) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4))
% 51.61/7.02      | l1_waybel_0(X3,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(X4,u1_struct_0(X3)) != iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(X3) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2673,c_4300]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_17405,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_4428]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_17826,plain,
% 51.61/7.02      ( v2_struct_0(X0) = iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_17405,c_33,c_34]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_17827,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_17826]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_5352,plain,
% 51.61/7.02      ( sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = X2
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_4420,c_2215]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_17868,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3)))
% 51.61/7.02      | sK5(X2,X3,sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))) = sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X2,X3)) = a_3_0_waybel_9(sK7,X0,X1)
% 51.61/7.02      | l1_waybel_0(X2,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(X2) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_17827,c_5352]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_26062,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_17868]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_26752,plain,
% 51.61/7.02      ( v2_struct_0(X0) = iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_26062,c_33,c_34]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_26753,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_26752]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_26758,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_26753]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_26801,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_26758,c_28,c_27,c_25,c_26762]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_26802,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_26801]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_24,plain,
% 51.61/7.02      ( ~ l1_waybel_0(X0,X1)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | m1_subset_1(sK6(X3,X0,X2),u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
% 51.61/7.02      | ~ l1_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(X0) ),
% 51.61/7.02      inference(cnf_transformation,[],[f64]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_603,plain,
% 51.61/7.02      ( ~ l1_waybel_0(X0,X1)
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 51.61/7.02      | m1_subset_1(sK6(X3,X0,X2),u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | sK7 != X1 ),
% 51.61/7.02      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_604,plain,
% 51.61/7.02      ( ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | v2_struct_0(sK7) ),
% 51.61/7.02      inference(unflattening,[status(thm)],[c_603]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_608,plain,
% 51.61/7.02      ( v2_struct_0(X0)
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ l1_waybel_0(X0,sK7) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_604,c_30]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_609,plain,
% 51.61/7.02      ( ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | v2_struct_0(X0) ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_608]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2197,plain,
% 51.61/7.02      ( l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0)) = iProver_top
% 51.61/7.02      | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_22,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
% 51.61/7.02      | ~ l1_waybel_0(X0,X3)
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
% 51.61/7.02      | ~ l1_struct_0(X3)
% 51.61/7.02      | v2_struct_0(X3)
% 51.61/7.02      | v2_struct_0(X0) ),
% 51.61/7.02      inference(cnf_transformation,[],[f66]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_675,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
% 51.61/7.02      | ~ l1_waybel_0(X0,X3)
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | v2_struct_0(X3)
% 51.61/7.02      | sK7 != X3 ),
% 51.61/7.02      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_676,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
% 51.61/7.02      | ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | v2_struct_0(X0)
% 51.61/7.02      | v2_struct_0(sK7) ),
% 51.61/7.02      inference(unflattening,[status(thm)],[c_675]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_680,plain,
% 51.61/7.02      ( v2_struct_0(X0)
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | r1_orders_2(X0,X1,sK6(X2,X0,X1)) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_676,c_30]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_681,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
% 51.61/7.02      | ~ l1_waybel_0(X0,sK7)
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 51.61/7.02      | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | v2_struct_0(X0) ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_680]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2194,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,sK6(X2,X0,X1)) = iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3147,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,X2) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(X2,X3) = iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X3) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2193,c_2216]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3261,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | r1_orders_2(X0,X1,X3) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(X3,X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2673,c_3147]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_6514,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK6(X3,X0,X1),u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(X3,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
% 51.61/7.02      | r2_hidden(sK6(X3,X0,X1),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2194,c_3261]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_6702,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(X3,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
% 51.61/7.02      | r2_hidden(sK6(X3,X0,X1),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2197,c_6514]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_6929,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X3),X0,X1),X2) = iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X3) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2217,c_6702]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_7426,plain,
% 51.61/7.02      ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),X3,X4) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4))
% 51.61/7.02      | l1_waybel_0(X3,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(X4,u1_struct_0(X3)) != iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(X3) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_6929,c_2196]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_8189,plain,
% 51.61/7.02      ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_7426]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_8202,plain,
% 51.61/7.02      ( v2_struct_0(X0) = iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_8189,c_33,c_34]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_8203,plain,
% 51.61/7.02      ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_8202]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_8217,plain,
% 51.61/7.02      ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3))),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3))),X0,X1)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(X2,X3,sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))) = sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X2,X3)) = a_3_0_waybel_9(sK7,X0,X1)
% 51.61/7.02      | l1_waybel_0(X2,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(X2) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_8203,c_5352]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32547,plain,
% 51.61/7.02      ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_8217]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32570,plain,
% 51.61/7.02      ( v2_struct_0(X0) = iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_32547,c_33,c_34]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32571,plain,
% 51.61/7.02      ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_32570]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32576,plain,
% 51.61/7.02      ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_32571]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32582,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | v2_struct_0(sK8)
% 51.61/7.02      | sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
% 51.61/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_32576]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32622,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_32576,c_28,c_27,c_25,c_32582]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32623,plain,
% 51.61/7.02      ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_32622]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32624,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_32623,c_2197]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_35,plain,
% 51.61/7.02      ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32639,plain,
% 51.61/7.02      ( r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_32624,c_33,c_34,c_35]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32640,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_32639]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32657,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_26802,c_32640]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2274,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 51.61/7.02      | m1_subset_1(sK6(X1,sK8,X0),u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_609]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2342,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | m1_subset_1(sK6(X0,sK8,sK9),u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2274]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2564,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2342]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2565,plain,
% 51.61/7.02      ( l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_2564]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32739,plain,
% 51.61/7.02      ( m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_32657,c_33,c_34,c_35,c_2565]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_70825,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_70819,c_32739]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_71189,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2217,c_70825]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32625,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_32623,c_2194]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32841,plain,
% 51.61/7.02      ( r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_32625,c_33,c_34,c_35]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32842,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
% 51.61/7.02      | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_32841]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32859,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_26802,c_32842]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2292,plain,
% 51.61/7.02      ( r1_orders_2(sK8,X0,sK6(X1,sK8,X0))
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_681]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2374,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK6(X0,sK8,sK9))
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2292]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2563,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9))
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2374]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2567,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_2563]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_32977,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_32859,c_33,c_34,c_35,c_2567]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_70824,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_70819,c_32977]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2280,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
% 51.61/7.02      | v2_struct_0(sK8)
% 51.61/7.02      | sK6(X1,sK8,X0) = X1 ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_634]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2358,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8)
% 51.61/7.02      | sK6(X0,sK8,sK9) = X0 ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2280]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2562,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2358]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2569,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_2562]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_1727,plain,( X0 = X0 ),theory(equality) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_7187,plain,
% 51.61/7.02      ( sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_1727]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_1728,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4418,plain,
% 51.61/7.02      ( X0 != X1
% 51.61/7.02      | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != X1
% 51.61/7.02      | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = X0 ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_1728]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_7194,plain,
% 51.61/7.02      ( X0 != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = X0
% 51.61/7.02      | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_4418]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_16969,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
% 51.61/7.02      | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_7194]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_1735,plain,
% 51.61/7.02      ( ~ r1_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X3) | X3 != X2 ),
% 51.61/7.02      theory(equality) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2513,plain,
% 51.61/7.02      ( ~ r1_orders_2(sK8,sK9,X0) | r1_orders_2(sK8,sK9,X1) | X1 != X0 ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_1735]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4686,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,X0)
% 51.61/7.02      | ~ r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9))
% 51.61/7.02      | X0 != sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2513]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_42661,plain,
% 51.61/7.02      ( ~ r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))))
% 51.61/7.02      | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_4686]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_42663,plain,
% 51.61/7.02      ( sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) != iProver_top
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_42661]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_71151,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_70824,c_33,c_34,c_35,c_2569,c_7187,c_16969,c_32977,
% 51.61/7.02                 c_42663]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_71155,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2217,c_71151]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_14,plain,
% 51.61/7.02      ( ~ sP0(X0,X1,X2,X3)
% 51.61/7.02      | ~ r1_orders_2(X1,X3,X4)
% 51.61/7.02      | ~ m1_subset_1(X4,u1_struct_0(X1))
% 51.61/7.02      | r2_hidden(X4,u1_struct_0(X0)) ),
% 51.61/7.02      inference(cnf_transformation,[],[f78]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2210,plain,
% 51.61/7.02      ( sP0(X0,X1,X2,X3) != iProver_top
% 51.61/7.02      | r1_orders_2(X1,X3,X4) != iProver_top
% 51.61/7.02      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | r2_hidden(X4,u1_struct_0(X0)) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3892,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,X2) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_3153,c_2210]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_0,plain,
% 51.61/7.02      ( ~ r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1) ),
% 51.61/7.02      inference(cnf_transformation,[],[f45]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2218,plain,
% 51.61/7.02      ( r2_hidden(sK2(X0,X1),X1) != iProver_top
% 51.61/7.02      | r1_tarski(X0,X1) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_5179,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,sK2(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1)))) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK2(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))),u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_3892,c_2218]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72431,plain,
% 51.61/7.02      ( l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_71155,c_5179]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72438,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_71189,c_33,c_34,c_35,c_72431]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72442,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_72438,c_2215]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72481,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_72438,c_5352]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72548,plain,
% 51.61/7.02      ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_72442,c_33,c_34,c_35,c_25,c_72481]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_15,plain,
% 51.61/7.02      ( ~ sP0(X0,X1,X2,X3)
% 51.61/7.02      | r1_orders_2(X1,X3,sK5(X1,X3,X4))
% 51.61/7.02      | ~ r2_hidden(X4,u1_struct_0(X0)) ),
% 51.61/7.02      inference(cnf_transformation,[],[f53]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2209,plain,
% 51.61/7.02      ( sP0(X0,X1,X2,X3) != iProver_top
% 51.61/7.02      | r1_orders_2(X1,X3,sK5(X1,X3,X4)) = iProver_top
% 51.61/7.02      | r2_hidden(X4,u1_struct_0(X0)) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3786,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,sK5(X0,X1,X2)) = iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_3153,c_2209]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4903,plain,
% 51.61/7.02      ( r1_orders_2(X0,X1,sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))) = iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2217,c_3786]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2627,plain,
% 51.61/7.02      ( sK6(X0,X1,X2) = X0
% 51.61/7.02      | r1_orders_2(X1,X2,X0) != iProver_top
% 51.61/7.02      | l1_waybel_0(X1,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | v2_struct_0(X1) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2193,c_2196]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_5308,plain,
% 51.61/7.02      ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_4903,c_2627]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_17,plain,
% 51.61/7.02      ( ~ sP0(X0,X1,X2,X3)
% 51.61/7.02      | m1_subset_1(sK5(X1,X3,X4),u1_struct_0(X1))
% 51.61/7.02      | ~ r2_hidden(X4,u1_struct_0(X0)) ),
% 51.61/7.02      inference(cnf_transformation,[],[f51]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2207,plain,
% 51.61/7.02      ( sP0(X0,X1,X2,X3) != iProver_top
% 51.61/7.02      | m1_subset_1(sK5(X1,X3,X4),u1_struct_0(X1)) = iProver_top
% 51.61/7.02      | r2_hidden(X4,u1_struct_0(X0)) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3781,plain,
% 51.61/7.02      ( l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) = iProver_top
% 51.61/7.02      | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_3153,c_2207]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4896,plain,
% 51.61/7.02      ( l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),u1_struct_0(X0)) = iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2217,c_3781]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64538,plain,
% 51.61/7.02      ( m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_5308,c_4896]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64539,plain,
% 51.61/7.02      ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_64538]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64544,plain,
% 51.61/7.02      ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = X2
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_64539,c_2215]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64994,plain,
% 51.61/7.02      ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,X2,X3))),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,X2,X3)))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X2,X3),a_3_0_waybel_9(sK7,sK8,sK9)),X2,X3) = sK2(a_3_0_waybel_9(sK7,X2,X3),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X2,X3),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X2,X3),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,X2,X3)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(X2,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_17827,c_64544]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_67028,plain,
% 51.61/7.02      ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_64994]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_67063,plain,
% 51.61/7.02      ( v2_struct_0(X0) = iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_67028,c_33,c_34]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_67064,plain,
% 51.61/7.02      ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_67063]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_67069,plain,
% 51.61/7.02      ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_67064]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2255,plain,
% 51.61/7.02      ( ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_3]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2306,plain,
% 51.61/7.02      ( r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_1]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2415,plain,
% 51.61/7.02      ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_1]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2593,plain,
% 51.61/7.02      ( ~ sP0(X0,sK8,X1,X2)
% 51.61/7.02      | m1_subset_1(sK5(sK8,X2,X3),u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(X3,u1_struct_0(X0)) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_17]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3129,plain,
% 51.61/7.02      ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,X0,X1)
% 51.61/7.02      | m1_subset_1(sK5(sK8,X1,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2593]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3368,plain,
% 51.61/7.02      ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9)
% 51.61/7.02      | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_3129]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2806,plain,
% 51.61/7.02      ( ~ sP0(X0,sK8,X1,sK9)
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK5(sK8,sK9,X2))
% 51.61/7.02      | ~ r2_hidden(X2,u1_struct_0(X0)) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_15]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3847,plain,
% 51.61/7.02      ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,X0,sK9)
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))))
% 51.61/7.02      | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2806]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3849,plain,
% 51.61/7.02      ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9)
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))))
% 51.61/7.02      | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_3847]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4148,plain,
% 51.61/7.02      ( ~ sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_7]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2286,plain,
% 51.61/7.02      ( sP1(X0,sK7,X1,k4_waybel_9(sK7,sK8,X2))
% 51.61/7.02      | ~ l1_waybel_0(X1,sK7)
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 51.61/7.02      | ~ m1_subset_1(X2,u1_struct_0(sK8))
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_578]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3562,plain,
% 51.61/7.02      ( sP1(X0,sK7,X1,k4_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | ~ l1_waybel_0(X1,sK7)
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | v2_struct_0(X1)
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2286]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4474,plain,
% 51.61/7.02      ( sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_3562]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2299,plain,
% 51.61/7.02      ( ~ r1_orders_2(sK8,X0,X1)
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 51.61/7.02      | r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_706]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2392,plain,
% 51.61/7.02      ( ~ r1_orders_2(sK8,sK9,X0)
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2299]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2508,plain,
% 51.61/7.02      ( ~ r1_orders_2(sK8,sK9,sK5(sK8,sK9,X0))
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK5(sK8,sK9,X0),u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | r2_hidden(sK5(sK8,sK9,X0),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2392]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_5001,plain,
% 51.61/7.02      ( ~ r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))))
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2508]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_9433,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8)
% 51.61/7.02      | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2358]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_67268,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_67069,c_33,c_34,c_35,c_25,c_2256,c_2307,c_2416,c_2569,
% 51.61/7.02                 c_3369,c_3850,c_4149,c_4475,c_5002,c_9440]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_67269,plain,
% 51.61/7.02      ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_67268]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72558,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK6(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(demodulation,[status(thm)],[c_72548,c_67269]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_73055,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_72558,c_2197]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2307,plain,
% 51.61/7.02      ( r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_2306]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2414,plain,
% 51.61/7.02      ( ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_0]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2418,plain,
% 51.61/7.02      ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2313,plain,
% 51.61/7.02      ( ~ r1_tarski(X0,a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),X0)
% 51.61/7.02      | a_3_0_waybel_9(sK7,sK8,sK9) = X0 ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_3]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2571,plain,
% 51.61/7.02      ( ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | a_3_0_waybel_9(sK7,sK8,sK9) = u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2313]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2572,plain,
% 51.61/7.02      ( a_3_0_waybel_9(sK7,sK8,sK9) = u1_struct_0(k4_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_2571]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2258,plain,
% 51.61/7.02      ( a_3_0_waybel_9(sK7,sK8,sK9) != X0
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != X0
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_1728]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3213,plain,
% 51.61/7.02      ( a_3_0_waybel_9(sK7,sK8,sK9) != u1_struct_0(k4_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2258]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4197,plain,
% 51.61/7.02      ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_1727]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_73206,plain,
% 51.61/7.02      ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_73055,c_33,c_34,c_35,c_25,c_2307,c_2418,c_2569,c_2572,
% 51.61/7.02                 c_3213,c_4197]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_73207,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_73206]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_73210,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2193,c_73207]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2815,plain,
% 51.61/7.02      ( sK6(sK6(X0,X1,X2),X1,X2) = sK6(X0,X1,X2)
% 51.61/7.02      | l1_waybel_0(X1,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | r2_hidden(X0,a_3_0_waybel_9(sK7,X1,X2)) != iProver_top
% 51.61/7.02      | v2_struct_0(X1) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2194,c_2627]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2898,plain,
% 51.61/7.02      ( sK6(sK6(X0,X1,X2),X1,X2) = sK6(X0,X1,X2)
% 51.61/7.02      | l1_waybel_0(X1,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | r2_hidden(X0,a_3_0_waybel_9(sK7,X1,X2)) != iProver_top
% 51.61/7.02      | v2_struct_0(X1) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2197,c_2815]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3006,plain,
% 51.61/7.02      ( sK6(sK6(X0,X1,X2),X1,X2) = sK6(X0,X1,X2)
% 51.61/7.02      | r1_orders_2(X1,X2,X0) != iProver_top
% 51.61/7.02      | l1_waybel_0(X1,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 51.61/7.02      | v2_struct_0(X1) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2193,c_2898]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_5307,plain,
% 51.61/7.02      ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_4903,c_3006]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_61628,plain,
% 51.61/7.02      ( m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_5307,c_4896]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_61629,plain,
% 51.61/7.02      ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_61628]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_61634,plain,
% 51.61/7.02      ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = X2
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_61629,c_2215]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_62065,plain,
% 51.61/7.02      ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,X2,X3))),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,X2,X3))),X0,X1)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X2,X3),a_3_0_waybel_9(sK7,sK8,sK9)),X2,X3) = sK2(a_3_0_waybel_9(sK7,X2,X3),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X2,X3),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X2,X3),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,X2,X3)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(X2,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X2) = iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_17827,c_61634]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64317,plain,
% 51.61/7.02      ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_62065]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64358,plain,
% 51.61/7.02      ( v2_struct_0(X0) = iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_64317,c_33,c_34]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64359,plain,
% 51.61/7.02      ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
% 51.61/7.02      | l1_waybel_0(X0,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 51.61/7.02      | v2_struct_0(X0) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_64358]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64364,plain,
% 51.61/7.02      ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_2206,c_64359]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2256,plain,
% 51.61/7.02      ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
% 51.61/7.02      | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_2255]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2416,plain,
% 51.61/7.02      ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_2415]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2584,plain,
% 51.61/7.02      ( ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | a_3_0_waybel_9(sK7,sK8,sK9) = a_3_0_waybel_9(sK7,sK8,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2313]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_5,plain,
% 51.61/7.02      ( r1_tarski(X0,X0) ),
% 51.61/7.02      inference(cnf_transformation,[],[f75]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2832,plain,
% 51.61/7.02      ( r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_5]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3369,plain,
% 51.61/7.02      ( sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) != iProver_top
% 51.61/7.02      | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_3368]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3848,plain,
% 51.61/7.02      ( sP0(k4_waybel_9(sK7,sK8,sK9),sK8,X0,sK9) != iProver_top
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_3847]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_3850,plain,
% 51.61/7.02      ( sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) != iProver_top
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_3848]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4149,plain,
% 51.61/7.02      ( sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_4148]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_4475,plain,
% 51.61/7.02      ( sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9)) = iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_4474]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_5002,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) != iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_5001]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_9440,plain,
% 51.61/7.02      ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_9433]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_19455,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8)
% 51.61/7.02      | sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2358]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_1729,plain,
% 51.61/7.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.61/7.02      theory(equality) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2481,plain,
% 51.61/7.02      ( ~ r2_hidden(X0,X1)
% 51.61/7.02      | r2_hidden(X2,a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | X2 != X0
% 51.61/7.02      | a_3_0_waybel_9(sK7,sK8,sK9) != X1 ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_1729]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_2953,plain,
% 51.61/7.02      ( ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | X1 != X0
% 51.61/7.02      | a_3_0_waybel_9(sK7,sK8,sK9) != a_3_0_waybel_9(sK7,sK8,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2481]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_9432,plain,
% 51.61/7.02      ( r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | X0 != sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | a_3_0_waybel_9(sK7,sK8,sK9) != a_3_0_waybel_9(sK7,sK8,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2953]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_33482,plain,
% 51.61/7.02      ( r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) != sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | a_3_0_waybel_9(sK7,sK8,sK9) != a_3_0_waybel_9(sK7,sK8,sK9) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_9432]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64391,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_64364,c_33,c_34,c_35,c_25,c_2256,c_2307,c_2416,c_2569,
% 51.61/7.02                 c_2584,c_2832,c_3369,c_3850,c_4149,c_4475,c_5002,c_9440,
% 51.61/7.02                 c_19462,c_33483]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64392,plain,
% 51.61/7.02      ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_64391]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64394,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_64392,c_2197]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_9435,plain,
% 51.61/7.02      ( ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2342]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_9436,plain,
% 51.61/7.02      ( l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_9435]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_66639,plain,
% 51.61/7.02      ( m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_64394,c_33,c_34,c_35,c_25,c_2307,c_2416,c_2569,c_2572,
% 51.61/7.02                 c_3213,c_3369,c_3850,c_4149,c_4197,c_4475,c_5002,c_9436]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_66640,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
% 51.61/7.02      inference(renaming,[status(thm)],[c_66639]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_67282,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_67269,c_66640]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72556,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) = iProver_top ),
% 51.61/7.02      inference(demodulation,[status(thm)],[c_72548,c_67282]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72566,plain,
% 51.61/7.02      ( m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_72556]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_64395,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_64392,c_2194]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_9434,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9))
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
% 51.61/7.02      | v2_struct_0(sK8) ),
% 51.61/7.02      inference(instantiation,[status(thm)],[c_2374]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_9438,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(predicate_to_equality,[status(thm)],[c_9434]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_66806,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_64395,c_33,c_34,c_35,c_25,c_2256,c_2307,c_2416,c_2569,
% 51.61/7.02                 c_3369,c_3850,c_4149,c_4475,c_5002,c_9438]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_67281,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_67269,c_66806]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72557,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = iProver_top ),
% 51.61/7.02      inference(demodulation,[status(thm)],[c_72548,c_67281]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72567,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_72557]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_73213,plain,
% 51.61/7.02      ( ~ r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
% 51.61/7.02      | ~ l1_waybel_0(sK8,sK7)
% 51.61/7.02      | ~ m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8))
% 51.61/7.02      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
% 51.61/7.02      | v2_struct_0(sK8)
% 51.61/7.02      | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_73210]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_73277,plain,
% 51.61/7.02      ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
% 51.61/7.02      inference(global_propositional_subsumption,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_73210,c_28,c_27,c_26,c_72566,c_72567,c_73213]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_73281,plain,
% 51.61/7.02      ( m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
% 51.61/7.02      inference(demodulation,[status(thm)],[c_73277,c_32739]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72573,plain,
% 51.61/7.02      ( l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) = iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_72548,c_4896]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(c_72572,plain,
% 51.61/7.02      ( r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = iProver_top
% 51.61/7.02      | l1_waybel_0(sK8,sK7) != iProver_top
% 51.61/7.02      | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
% 51.61/7.02      | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
% 51.61/7.02      | v2_struct_0(sK8) = iProver_top ),
% 51.61/7.02      inference(superposition,[status(thm)],[c_72548,c_4903]) ).
% 51.61/7.02  
% 51.61/7.02  cnf(contradiction,plain,
% 51.61/7.02      ( $false ),
% 51.61/7.02      inference(minisat,
% 51.61/7.02                [status(thm)],
% 51.61/7.02                [c_77642,c_73281,c_72573,c_72572,c_72431,c_2418,c_2307,
% 51.61/7.02                 c_2256,c_25,c_35,c_34,c_33]) ).
% 51.61/7.02  
% 51.61/7.02  
% 51.61/7.02  % SZS output end CNFRefutation for theBenchmark.p
% 51.61/7.02  
% 51.61/7.02  ------                               Statistics
% 51.61/7.02  
% 51.61/7.02  ------ General
% 51.61/7.02  
% 51.61/7.02  abstr_ref_over_cycles:                  0
% 51.61/7.02  abstr_ref_under_cycles:                 0
% 51.61/7.02  gc_basic_clause_elim:                   0
% 51.61/7.02  forced_gc_time:                         0
% 51.61/7.02  parsing_time:                           0.009
% 51.61/7.02  unif_index_cands_time:                  0.
% 51.61/7.02  unif_index_add_time:                    0.
% 51.61/7.02  orderings_time:                         0.
% 51.61/7.02  out_proof_time:                         0.081
% 51.61/7.02  total_time:                             6.44
% 51.61/7.02  num_of_symbols:                         57
% 51.61/7.02  num_of_terms:                           60408
% 51.61/7.02  
% 51.61/7.02  ------ Preprocessing
% 51.61/7.02  
% 51.61/7.02  num_of_splits:                          0
% 51.61/7.02  num_of_split_atoms:                     0
% 51.61/7.02  num_of_reused_defs:                     0
% 51.61/7.02  num_eq_ax_congr_red:                    78
% 51.61/7.02  num_of_sem_filtered_clauses:            1
% 51.61/7.02  num_of_subtypes:                        0
% 51.61/7.02  monotx_restored_types:                  0
% 51.61/7.02  sat_num_of_epr_types:                   0
% 51.61/7.02  sat_num_of_non_cyclic_types:            0
% 51.61/7.02  sat_guarded_non_collapsed_types:        0
% 51.61/7.02  num_pure_diseq_elim:                    0
% 51.61/7.02  simp_replaced_by:                       0
% 51.61/7.02  res_preprocessed:                       138
% 51.61/7.02  prep_upred:                             0
% 51.61/7.02  prep_unflattend:                        77
% 51.61/7.02  smt_new_axioms:                         0
% 51.61/7.02  pred_elim_cands:                        8
% 51.61/7.02  pred_elim:                              3
% 51.61/7.02  pred_elim_cl:                           3
% 51.61/7.02  pred_elim_cycles:                       8
% 51.61/7.02  merged_defs:                            0
% 51.61/7.02  merged_defs_ncl:                        0
% 51.61/7.02  bin_hyper_res:                          0
% 51.61/7.02  prep_cycles:                            4
% 51.61/7.02  pred_elim_time:                         0.017
% 51.61/7.02  splitting_time:                         0.
% 51.61/7.02  sem_filter_time:                        0.
% 51.61/7.02  monotx_time:                            0.
% 51.61/7.02  subtype_inf_time:                       0.
% 51.61/7.02  
% 51.61/7.02  ------ Problem properties
% 51.61/7.02  
% 51.61/7.02  clauses:                                27
% 51.61/7.02  conjectures:                            5
% 51.61/7.02  epr:                                    6
% 51.61/7.02  horn:                                   17
% 51.61/7.02  ground:                                 5
% 51.61/7.02  unary:                                  6
% 51.61/7.02  binary:                                 4
% 51.61/7.02  lits:                                   89
% 51.61/7.02  lits_eq:                                11
% 51.61/7.02  fd_pure:                                0
% 51.61/7.02  fd_pseudo:                              0
% 51.61/7.02  fd_cond:                                0
% 51.61/7.02  fd_pseudo_cond:                         2
% 51.61/7.02  ac_symbols:                             0
% 51.61/7.02  
% 51.61/7.02  ------ Propositional Solver
% 51.61/7.02  
% 51.61/7.02  prop_solver_calls:                      59
% 51.61/7.02  prop_fast_solver_calls:                 5998
% 51.61/7.02  smt_solver_calls:                       0
% 51.61/7.02  smt_fast_solver_calls:                  0
% 51.61/7.02  prop_num_of_clauses:                    54189
% 51.61/7.02  prop_preprocess_simplified:             35870
% 51.61/7.02  prop_fo_subsumed:                       238
% 51.61/7.02  prop_solver_time:                       0.
% 51.61/7.02  smt_solver_time:                        0.
% 51.61/7.02  smt_fast_solver_time:                   0.
% 51.61/7.02  prop_fast_solver_time:                  0.
% 51.61/7.02  prop_unsat_core_time:                   0.004
% 51.61/7.02  
% 51.61/7.02  ------ QBF
% 51.61/7.02  
% 51.61/7.02  qbf_q_res:                              0
% 51.61/7.02  qbf_num_tautologies:                    0
% 51.61/7.02  qbf_prep_cycles:                        0
% 51.61/7.02  
% 51.61/7.02  ------ BMC1
% 51.61/7.02  
% 51.61/7.02  bmc1_current_bound:                     -1
% 51.61/7.02  bmc1_last_solved_bound:                 -1
% 51.61/7.02  bmc1_unsat_core_size:                   -1
% 51.61/7.02  bmc1_unsat_core_parents_size:           -1
% 51.61/7.02  bmc1_merge_next_fun:                    0
% 51.61/7.02  bmc1_unsat_core_clauses_time:           0.
% 51.61/7.02  
% 51.61/7.02  ------ Instantiation
% 51.61/7.02  
% 51.61/7.02  inst_num_of_clauses:                    55
% 51.61/7.02  inst_num_in_passive:                    22
% 51.61/7.02  inst_num_in_active:                     1933
% 51.61/7.02  inst_num_in_unprocessed:                8
% 51.61/7.02  inst_num_of_loops:                      3028
% 51.61/7.02  inst_num_of_learning_restarts:          1
% 51.61/7.02  inst_num_moves_active_passive:          1084
% 51.61/7.02  inst_lit_activity:                      0
% 51.61/7.02  inst_lit_activity_moves:                1
% 51.61/7.02  inst_num_tautologies:                   0
% 51.61/7.02  inst_num_prop_implied:                  0
% 51.61/7.02  inst_num_existing_simplified:           0
% 51.61/7.02  inst_num_eq_res_simplified:             0
% 51.61/7.02  inst_num_child_elim:                    0
% 51.61/7.02  inst_num_of_dismatching_blockings:      2797
% 51.61/7.02  inst_num_of_non_proper_insts:           5781
% 51.61/7.02  inst_num_of_duplicates:                 0
% 51.61/7.02  inst_inst_num_from_inst_to_res:         0
% 51.61/7.02  inst_dismatching_checking_time:         0.
% 51.61/7.02  
% 51.61/7.02  ------ Resolution
% 51.61/7.02  
% 51.61/7.02  res_num_of_clauses:                     40
% 51.61/7.02  res_num_in_passive:                     40
% 51.61/7.02  res_num_in_active:                      0
% 51.61/7.02  res_num_of_loops:                       142
% 51.61/7.02  res_forward_subset_subsumed:            318
% 51.61/7.02  res_backward_subset_subsumed:           0
% 51.61/7.02  res_forward_subsumed:                   0
% 51.61/7.02  res_backward_subsumed:                  0
% 51.61/7.02  res_forward_subsumption_resolution:     3
% 51.61/7.02  res_backward_subsumption_resolution:    0
% 51.61/7.02  res_clause_to_clause_subsumption:       140680
% 51.61/7.02  res_orphan_elimination:                 0
% 51.61/7.02  res_tautology_del:                      524
% 51.61/7.02  res_num_eq_res_simplified:              0
% 51.61/7.02  res_num_sel_changes:                    0
% 51.61/7.02  res_moves_from_active_to_pass:          0
% 51.61/7.02  
% 51.61/7.02  ------ Superposition
% 51.61/7.02  
% 51.61/7.02  sup_time_total:                         0.
% 51.61/7.02  sup_time_generating:                    0.
% 51.61/7.02  sup_time_sim_full:                      0.
% 51.61/7.02  sup_time_sim_immed:                     0.
% 51.61/7.02  
% 51.61/7.02  sup_num_of_clauses:                     13584
% 51.61/7.02  sup_num_in_active:                      509
% 51.61/7.02  sup_num_in_passive:                     13075
% 51.61/7.02  sup_num_of_loops:                       604
% 51.61/7.02  sup_fw_superposition:                   6694
% 51.61/7.02  sup_bw_superposition:                   7927
% 51.61/7.02  sup_immediate_simplified:               459
% 51.61/7.02  sup_given_eliminated:                   12
% 51.61/7.02  comparisons_done:                       0
% 51.61/7.02  comparisons_avoided:                    1892
% 51.61/7.02  
% 51.61/7.02  ------ Simplifications
% 51.61/7.02  
% 51.61/7.02  
% 51.61/7.02  sim_fw_subset_subsumed:                 168
% 51.61/7.02  sim_bw_subset_subsumed:                 55
% 51.61/7.02  sim_fw_subsumed:                        240
% 51.61/7.02  sim_bw_subsumed:                        131
% 51.61/7.02  sim_fw_subsumption_res:                 0
% 51.61/7.02  sim_bw_subsumption_res:                 0
% 51.61/7.02  sim_tautology_del:                      14
% 51.61/7.02  sim_eq_tautology_del:                   80
% 51.61/7.02  sim_eq_res_simp:                        1
% 51.61/7.02  sim_fw_demodulated:                     0
% 51.61/7.02  sim_bw_demodulated:                     16
% 51.61/7.02  sim_light_normalised:                   0
% 51.61/7.02  sim_joinable_taut:                      0
% 51.61/7.02  sim_joinable_simp:                      0
% 51.61/7.02  sim_ac_normalised:                      0
% 51.61/7.02  sim_smt_subsumption:                    0
% 51.61/7.02  
%------------------------------------------------------------------------------
