%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2013+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:01 EST 2020

% Result     : Theorem 54.54s
% Output     : CNFRefutation 54.54s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_26766)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    l1_waybel_0(sK8,sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

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

cnf(c_704,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_waybel_0(X0,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_705,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_709,plain,
    ( v2_struct_0(X0)
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ r1_orders_2(X0,X1,X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_705,c_30])).

cnf(c_710,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_709])).

cnf(c_77438,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_77645,plain,
    ( ~ r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_77438])).

cnf(c_77646,plain,
    ( r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_77645])).

cnf(c_2197,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_4,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2219,plain,
    ( r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2210,plain,
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

cnf(c_336,plain,
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

cnf(c_337,plain,
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
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_19,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_361,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_337,c_19])).

cnf(c_576,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_361,c_29])).

cnf(c_577,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3))
    | ~ l1_waybel_0(X1,sK7)
    | ~ l1_waybel_0(X2,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_581,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_waybel_0(X2,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_30])).

cnf(c_582,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3))
    | ~ l1_waybel_0(X2,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_581])).

cnf(c_2202,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,X2,X3)) = iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))
    | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2216,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0)) != iProver_top
    | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3157,plain,
    ( sP0(k4_waybel_9(sK7,X0,X1),X0,sK7,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_2216])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,u1_struct_0(X0))
    | sK5(X1,X3,X4) = X4 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2212,plain,
    ( sK5(X0,X1,X2) = X2
    | sP0(X3,X0,X4,X1) != iProver_top
    | r2_hidden(X2,u1_struct_0(X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3255,plain,
    ( sK5(X0,X1,X2) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3157,c_2212])).

cnf(c_4424,plain,
    ( sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_3255])).

cnf(c_23,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | sK6(X3,X0,X2) = X3 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_632,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK6(X3,X0,X2) = X3
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_633,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | sK6(X2,X0,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_637,plain,
    ( v2_struct_0(X0)
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK7)
    | sK6(X2,X0,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_30])).

cnf(c_638,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | sK6(X2,X0,X1) = X2 ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_2200,plain,
    ( sK6(X0,X1,X2) = X0
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_3_0_waybel_9(sK7,X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_2677,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_2200])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2222,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2897,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | a_3_0_waybel_9(sK7,X0,X1) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2222])).

cnf(c_5357,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3))),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,X2,X3)))
    | sK5(X2,X3,sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))) = sK2(u1_struct_0(k4_waybel_9(sK7,X2,X3)),a_3_0_waybel_9(sK7,X0,X1))
    | u1_struct_0(k4_waybel_9(sK7,X2,X3)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4424,c_2897])).

cnf(c_70686,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_5357])).

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

cnf(c_70729,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_70686,c_33,c_34])).

cnf(c_70730,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_70729])).

cnf(c_70735,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_70730])).

cnf(c_25,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_70746,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_70735])).

cnf(c_70822,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_70735,c_28,c_27,c_25,c_70746])).

cnf(c_70823,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(renaming,[status(thm)],[c_70822])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2218,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3150,plain,
    ( r2_hidden(sK2(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_2218])).

cnf(c_4304,plain,
    ( sK6(sK2(X0,X1),X2,X3) = sK2(X0,X1)
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,a_3_0_waybel_9(sK7,X2,X3)) != iProver_top
    | v2_struct_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3150,c_2200])).

cnf(c_4432,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X3,X4) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4))
    | l1_waybel_0(X3,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X3)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_4304])).

cnf(c_17409,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_4432])).

cnf(c_17830,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17409,c_33,c_34])).

cnf(c_17831,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_17830])).

cnf(c_5356,plain,
    ( sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4424,c_2222])).

cnf(c_17872,plain,
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
    inference(superposition,[status(thm)],[c_17831,c_5356])).

cnf(c_26066,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_17872])).

cnf(c_26756,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26066,c_33,c_34])).

cnf(c_26757,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1)))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_26756])).

cnf(c_26762,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_26757])).

cnf(c_26805,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26762,c_28,c_27,c_25,c_26766])).

cnf(c_26806,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(renaming,[status(thm)],[c_26805])).

cnf(c_24,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X3,X0,X2),u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_607,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK6(X3,X0,X2),u1_struct_0(X0))
    | ~ r2_hidden(X3,a_3_0_waybel_9(X1,X0,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_608,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_607])).

cnf(c_612,plain,
    ( v2_struct_0(X0)
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_608,c_30])).

cnf(c_613,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_612])).

cnf(c_2201,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK6(X2,X0,X1),u1_struct_0(X0)) = iProver_top
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_22,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
    | ~ l1_waybel_0(X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
    | ~ l1_struct_0(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_679,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
    | ~ l1_waybel_0(X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(X3,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_680,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_684,plain,
    ( v2_struct_0(X0)
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK7)
    | r1_orders_2(X0,X1,sK6(X2,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_680,c_30])).

cnf(c_685,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_684])).

cnf(c_2198,plain,
    ( r1_orders_2(X0,X1,sK6(X2,X0,X1)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_3151,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,X3) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X3) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_2218])).

cnf(c_3265,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | r1_orders_2(X0,X1,X3) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_3151])).

cnf(c_6518,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK6(X3,X0,X1),u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | r2_hidden(sK6(X3,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_3265])).

cnf(c_6706,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X3,a_3_0_waybel_9(sK7,X0,X1)) != iProver_top
    | r2_hidden(sK6(X3,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2201,c_6518])).

cnf(c_6933,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),X2)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X3),X0,X1),X2) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X3) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_6706])).

cnf(c_7430,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),X3,X4) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,X3,X4))
    | l1_waybel_0(X3,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X3)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6933,c_2200])).

cnf(c_8193,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_7430])).

cnf(c_8206,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8193,c_33,c_34])).

cnf(c_8207,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),X2),X0,X1)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,X0,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8206])).

cnf(c_8221,plain,
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
    inference(superposition,[status(thm)],[c_8207,c_5356])).

cnf(c_32551,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_8221])).

cnf(c_32574,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32551,c_33,c_34])).

cnf(c_32575,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_32574])).

cnf(c_32580,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_32575])).

cnf(c_32586,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_32580])).

cnf(c_32626,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32580,c_28,c_27,c_25,c_32586])).

cnf(c_32627,plain,
    ( sK6(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(renaming,[status(thm)],[c_32626])).

cnf(c_32628,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_32627,c_2201])).

cnf(c_35,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32643,plain,
    ( r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32628,c_33,c_34,c_35])).

cnf(c_32644,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_32643])).

cnf(c_32661,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26806,c_32644])).

cnf(c_2278,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | m1_subset_1(sK6(X1,sK8,X0),u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_2346,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | m1_subset_1(sK6(X0,sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_2568,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_2569,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2568])).

cnf(c_32743,plain,
    ( m1_subset_1(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32661,c_33,c_34,c_35,c_2569])).

cnf(c_70829,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_70823,c_32743])).

cnf(c_71193,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_70829])).

cnf(c_32629,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_32627,c_2198])).

cnf(c_32845,plain,
    ( r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32629,c_33,c_34,c_35])).

cnf(c_32846,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | r2_hidden(sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_32845])).

cnf(c_32863,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26806,c_32846])).

cnf(c_2296,plain,
    ( r1_orders_2(sK8,X0,sK6(X1,sK8,X0))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_2378,plain,
    ( r1_orders_2(sK8,sK9,sK6(X0,sK8,sK9))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_2567,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_2571,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2567])).

cnf(c_32981,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32863,c_33,c_34,c_35,c_2571])).

cnf(c_70828,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_70823,c_32981])).

cnf(c_2284,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8)
    | sK6(X1,sK8,X0) = X1 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_2362,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | sK6(X0,sK8,sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_2284])).

cnf(c_2566,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_2573,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2566])).

cnf(c_1731,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7191,plain,
    ( sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_1732,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4422,plain,
    ( X0 != X1
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != X1
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = X0 ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_7198,plain,
    ( X0 != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = X0
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_4422])).

cnf(c_16973,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_7198])).

cnf(c_1739,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X3)
    | X3 != X2 ),
    theory(equality)).

cnf(c_2517,plain,
    ( ~ r1_orders_2(sK8,sK9,X0)
    | r1_orders_2(sK8,sK9,X1)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_4690,plain,
    ( r1_orders_2(sK8,sK9,X0)
    | ~ r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9))
    | X0 != sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2517])).

cnf(c_42665,plain,
    ( ~ r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9))
    | r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))))
    | sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_4690])).

cnf(c_42667,plain,
    ( sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | r1_orders_2(sK8,sK9,sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9)) != iProver_top
    | r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42665])).

cnf(c_71155,plain,
    ( r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_70828,c_33,c_34,c_35,c_2573,c_7191,c_16973,c_32981,c_42667])).

cnf(c_71159,plain,
    ( r1_orders_2(sK8,sK9,sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_71155])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | r2_hidden(X4,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2214,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_orders_2(X1,X3,X4) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X4,u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3896,plain,
    ( r1_orders_2(X0,X1,X2) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3157,c_2214])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2220,plain,
    ( r2_hidden(sK2(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5183,plain,
    ( r1_orders_2(X0,X1,sK2(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1)))) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK2(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))),u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3896,c_2220])).

cnf(c_72435,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_71159,c_5183])).

cnf(c_72442,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_71193,c_33,c_34,c_35,c_72435])).

cnf(c_72446,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_72442,c_2222])).

cnf(c_72485,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_72442,c_5356])).

cnf(c_72552,plain,
    ( sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_72446,c_33,c_34,c_35,c_25,c_72485])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_orders_2(X1,X3,sK5(X1,X3,X4))
    | ~ r2_hidden(X4,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2213,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_orders_2(X1,X3,sK5(X1,X3,X4)) = iProver_top
    | r2_hidden(X4,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3790,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X1,X2)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3157,c_2213])).

cnf(c_4907,plain,
    ( r1_orders_2(X0,X1,sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_3790])).

cnf(c_2631,plain,
    ( sK6(X0,X1,X2) = X0
    | r1_orders_2(X1,X2,X0) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_2200])).

cnf(c_5312,plain,
    ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4907,c_2631])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | m1_subset_1(sK5(X1,X3,X4),u1_struct_0(X1))
    | ~ r2_hidden(X4,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2211,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | m1_subset_1(sK5(X1,X3,X4),u1_struct_0(X1)) = iProver_top
    | r2_hidden(X4,u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3785,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) = iProver_top
    | r2_hidden(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3157,c_2211])).

cnf(c_4900,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),u1_struct_0(X0)) = iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_3785])).

cnf(c_64542,plain,
    ( m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5312,c_4900])).

cnf(c_64543,plain,
    ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_64542])).

cnf(c_64548,plain,
    ( sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1) = sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2))
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_64543,c_2222])).

cnf(c_64998,plain,
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
    inference(superposition,[status(thm)],[c_17831,c_64548])).

cnf(c_67032,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1)))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_64998])).

cnf(c_67067,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1)))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_67032,c_33,c_34])).

cnf(c_67068,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1)))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_67067])).

cnf(c_67073,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_67068])).

cnf(c_2259,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2310,plain,
    ( r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2419,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2597,plain,
    ( ~ sP0(X0,sK8,X1,X2)
    | m1_subset_1(sK5(sK8,X2,X3),u1_struct_0(sK8))
    | ~ r2_hidden(X3,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3133,plain,
    ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,X0,X1)
    | m1_subset_1(sK5(sK8,X1,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8))
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_2597])).

cnf(c_3372,plain,
    ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9)
    | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8))
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_3133])).

cnf(c_2810,plain,
    ( ~ sP0(X0,sK8,X1,sK9)
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,X2))
    | ~ r2_hidden(X2,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3851,plain,
    ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,X0,sK9)
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))))
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_2810])).

cnf(c_3853,plain,
    ( ~ sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9)
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))))
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_3851])).

cnf(c_4152,plain,
    ( ~ sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9))
    | sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2290,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,sK8,X2))
    | ~ l1_waybel_0(X1,sK7)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK8))
    | v2_struct_0(X1)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_3566,plain,
    ( sP1(X0,sK7,X1,k4_waybel_9(sK7,sK8,sK9))
    | ~ l1_waybel_0(X1,sK7)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | v2_struct_0(X1)
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2290])).

cnf(c_4478,plain,
    ( sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3566])).

cnf(c_2303,plain,
    ( ~ r1_orders_2(sK8,X0,X1)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,X0))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_2396,plain,
    ( ~ r1_orders_2(sK8,sK9,X0)
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2303])).

cnf(c_2512,plain,
    ( ~ r1_orders_2(sK8,sK9,sK5(sK8,sK9,X0))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK5(sK8,sK9,X0),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(sK5(sK8,sK9,X0),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2396])).

cnf(c_5005,plain,
    ( ~ r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2512])).

cnf(c_9437,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_67272,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_67073,c_33,c_34,c_35,c_25,c_2260,c_2311,c_2420,c_2573,c_3373,c_3854,c_4153,c_4479,c_5006,c_9444])).

cnf(c_67273,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(renaming,[status(thm)],[c_67272])).

cnf(c_72562,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(demodulation,[status(thm)],[c_72552,c_67273])).

cnf(c_73059,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_72562,c_2201])).

cnf(c_2311,plain,
    ( r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2310])).

cnf(c_2418,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2422,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2418])).

cnf(c_2317,plain,
    ( ~ r1_tarski(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),X0)
    | a_3_0_waybel_9(sK7,sK8,sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2575,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))
    | a_3_0_waybel_9(sK7,sK8,sK9) = u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_2317])).

cnf(c_2576,plain,
    ( a_3_0_waybel_9(sK7,sK8,sK9) = u1_struct_0(k4_waybel_9(sK7,sK8,sK9))
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2575])).

cnf(c_2262,plain,
    ( a_3_0_waybel_9(sK7,sK8,sK9) != X0
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != X0
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_3217,plain,
    ( a_3_0_waybel_9(sK7,sK8,sK9) != u1_struct_0(k4_waybel_9(sK7,sK8,sK9))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) != u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_2262])).

cnf(c_4201,plain,
    ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_73210,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_73059,c_33,c_34,c_35,c_25,c_2311,c_2422,c_2573,c_2576,c_3217,c_4201])).

cnf(c_73211,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(renaming,[status(thm)],[c_73210])).

cnf(c_73214,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_73211])).

cnf(c_2819,plain,
    ( sK6(sK6(X0,X1,X2),X1,X2) = sK6(X0,X1,X2)
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_3_0_waybel_9(sK7,X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_2631])).

cnf(c_2902,plain,
    ( sK6(sK6(X0,X1,X2),X1,X2) = sK6(X0,X1,X2)
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | r2_hidden(X0,a_3_0_waybel_9(sK7,X1,X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2201,c_2819])).

cnf(c_3010,plain,
    ( sK6(sK6(X0,X1,X2),X1,X2) = sK6(X0,X1,X2)
    | r1_orders_2(X1,X2,X0) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_2902])).

cnf(c_5311,plain,
    ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4907,c_3010])).

cnf(c_61632,plain,
    ( m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5311,c_4900])).

cnf(c_61633,plain,
    ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_61632])).

cnf(c_61638,plain,
    ( sK6(sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1),X0,X1) = sK6(sK5(X0,X1,sK2(u1_struct_0(k4_waybel_9(sK7,X0,X1)),X2)),X0,X1)
    | u1_struct_0(k4_waybel_9(sK7,X0,X1)) = X2
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_tarski(X2,u1_struct_0(k4_waybel_9(sK7,X0,X1))) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_61633,c_2222])).

cnf(c_62069,plain,
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
    inference(superposition,[status(thm)],[c_17831,c_61638])).

cnf(c_64321,plain,
    ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_62069])).

cnf(c_64362,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_64321,c_33,c_34])).

cnf(c_64363,plain,
    ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,X0,X1))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9)),X0,X1) = sK2(a_3_0_waybel_9(sK7,X0,X1),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,X0,X1),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,X0,X1)
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_64362])).

cnf(c_64368,plain,
    ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2210,c_64363])).

cnf(c_2260,plain,
    ( u1_struct_0(k4_waybel_9(sK7,sK8,sK9)) = a_3_0_waybel_9(sK7,sK8,sK9)
    | r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2259])).

cnf(c_2420,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) = iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2419])).

cnf(c_2588,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | a_3_0_waybel_9(sK7,sK8,sK9) = a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2317])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2836,plain,
    ( r1_tarski(a_3_0_waybel_9(sK7,sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3373,plain,
    ( sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3372])).

cnf(c_3852,plain,
    ( sP0(k4_waybel_9(sK7,sK8,sK9),sK8,X0,sK9) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3851])).

cnf(c_3854,plain,
    ( sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) != iProver_top
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) = iProver_top
    | r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3852])).

cnf(c_4153,plain,
    ( sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9)) != iProver_top
    | sP0(k4_waybel_9(sK7,sK8,sK9),sK8,sK7,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4152])).

cnf(c_4479,plain,
    ( sP1(sK9,sK7,sK8,k4_waybel_9(sK7,sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4478])).

cnf(c_5006,plain,
    ( r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5005])).

cnf(c_9444,plain,
    ( sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9437])).

cnf(c_19459,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8)
    | sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_1733,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2485,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,a_3_0_waybel_9(sK7,sK8,sK9))
    | X2 != X0
    | a_3_0_waybel_9(sK7,sK8,sK9) != X1 ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_2957,plain,
    ( ~ r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | r2_hidden(X1,a_3_0_waybel_9(sK7,sK8,sK9))
    | X1 != X0
    | a_3_0_waybel_9(sK7,sK8,sK9) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2485])).

cnf(c_9436,plain,
    ( r2_hidden(X0,a_3_0_waybel_9(sK7,sK8,sK9))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | X0 != sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | a_3_0_waybel_9(sK7,sK8,sK9) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_2957])).

cnf(c_33486,plain,
    ( r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) != sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | a_3_0_waybel_9(sK7,sK8,sK9) != a_3_0_waybel_9(sK7,sK8,sK9) ),
    inference(instantiation,[status(thm)],[c_9436])).

cnf(c_64395,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_64368,c_33,c_34,c_35,c_25,c_2260,c_2311,c_2420,c_2573,c_2588,c_2836,c_3373,c_3854,c_4153,c_4479,c_5006,c_9444,c_19466,c_33487])).

cnf(c_64396,plain,
    ( sK6(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),sK8,sK9) = sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(renaming,[status(thm)],[c_64395])).

cnf(c_64398,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_64396,c_2201])).

cnf(c_9439,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_9440,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9439])).

cnf(c_66643,plain,
    ( m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_64398,c_33,c_34,c_35,c_25,c_2311,c_2420,c_2573,c_2576,c_3217,c_3373,c_3854,c_4153,c_4201,c_4479,c_5006,c_9440])).

cnf(c_66644,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | m1_subset_1(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),u1_struct_0(sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_66643])).

cnf(c_67286,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | m1_subset_1(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_67273,c_66644])).

cnf(c_72560,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_72552,c_67286])).

cnf(c_72570,plain,
    ( m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_72560])).

cnf(c_64399,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_64396,c_2198])).

cnf(c_9438,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9))
    | v2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_9442,plain,
    ( r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9438])).

cnf(c_66810,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK6(sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))),sK8,sK9)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_64399,c_33,c_34,c_35,c_25,c_2260,c_2311,c_2420,c_2573,c_3373,c_3854,c_4153,c_4479,c_5006,c_9442])).

cnf(c_67285,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK5(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_67273,c_66810])).

cnf(c_72561,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9)))
    | r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_72552,c_67285])).

cnf(c_72571,plain,
    ( r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_72561])).

cnf(c_73217,plain,
    ( ~ r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | v2_struct_0(sK8)
    | sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_73214])).

cnf(c_73281,plain,
    ( sK6(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),sK8,sK9) = sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_73214,c_28,c_27,c_26,c_72570,c_72571,c_73217])).

cnf(c_73285,plain,
    ( m1_subset_1(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),u1_struct_0(sK8)) = iProver_top
    | r2_hidden(sK2(a_3_0_waybel_9(sK7,sK8,sK9),u1_struct_0(k4_waybel_9(sK7,sK8,sK9))),a_3_0_waybel_9(sK7,sK8,sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_73281,c_32743])).

cnf(c_72577,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)),u1_struct_0(sK8)) = iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_72552,c_4900])).

cnf(c_72576,plain,
    ( r1_orders_2(sK8,sK9,sK2(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9))) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK8)) != iProver_top
    | r1_tarski(u1_struct_0(k4_waybel_9(sK7,sK8,sK9)),a_3_0_waybel_9(sK7,sK8,sK9)) = iProver_top
    | v2_struct_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_72552,c_4907])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_77646,c_73285,c_72577,c_72576,c_72435,c_2422,c_2311,c_2260,c_25,c_35,c_34,c_33])).


%------------------------------------------------------------------------------
