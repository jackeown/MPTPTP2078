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
% DateTime   : Thu Dec  3 12:28:41 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 424 expanded)
%              Number of clauses        :   71 ( 123 expanded)
%              Number of leaves         :   17 ( 118 expanded)
%              Depth                    :   20
%              Number of atoms          :  641 (2474 expanded)
%              Number of equality atoms :  133 ( 267 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f32])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,sK8)),u1_struct_0(X1))
        & m1_subset_1(sK8,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,sK7,X2)),u1_struct_0(sK7))
            & m1_subset_1(X2,u1_struct_0(sK7)) )
        & l1_waybel_0(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK6,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK6)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))
    & m1_subset_1(sK8,u1_struct_0(sK7))
    & l1_waybel_0(sK7,sK6)
    & ~ v2_struct_0(sK7)
    & l1_struct_0(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f28,f45,f44,f43])).

fof(f73,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X2,X0,X1,X3] :
      ( ( k4_waybel_9(X0,X1,X2) = X3
      <=> sP0(X3,X1,X0,X2) )
      | ~ sP1(X2,X0,X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
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

fof(f31,plain,(
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
    inference(definition_folding,[],[f24,f30,f29])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X0,X1,X3)
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f34,plain,(
    ! [X2,X0,X1,X3] :
      ( ( ( k4_waybel_9(X0,X1,X2) = X3
          | ~ sP0(X3,X1,X0,X2) )
        & ( sP0(X3,X1,X0,X2)
          | k4_waybel_9(X0,X1,X2) != X3 ) )
      | ~ sP1(X2,X0,X1,X3) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k4_waybel_9(X1,X2,X0) = X3
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k4_waybel_9(X1,X2,X0) != X3 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f34])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k4_waybel_9(X1,X2,X0) != X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0)
      | ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X7,X3,X1] :
      ( ? [X9] :
          ( r1_orders_2(X1,X3,X9)
          & X7 = X9
          & m1_subset_1(X9,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X3,sK5(X1,X3,X7))
        & sK5(X1,X3,X7) = X7
        & m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X4,X3,X1,X0] :
      ( ? [X6] :
          ( r1_orders_2(X1,X3,X6)
          & X4 = X6
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r1_orders_2(X1,X3,sK4(X0,X1,X3))
        & sK4(X0,X1,X3) = X4
        & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f41,f40,f39])).

fof(f55,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1))
      | ~ r2_hidden(X7,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK5(X1,X3,X7) = X7
      | ~ r2_hidden(X7,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & ~ v1_xboole_0(u1_waybel_0(X0,X1))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_waybel_0(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_309,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | u1_struct_0(k4_waybel_9(sK6,sK7,sK8)) != X0
    | u1_struct_0(sK7) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_310,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8))) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_2810,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8))) ),
    inference(subtyping,[status(esa)],[c_310])).

cnf(c_3329,plain,
    ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2810])).

cnf(c_18,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ v6_waybel_0(X3,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,plain,
    ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_327,plain,
    ( sP1(X0,X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(X4,X5)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X5)
    | X5 != X1
    | k4_waybel_9(X5,X4,X6) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_328,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_waybel_0(k4_waybel_9(X1,X3,X4),X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_19,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_352,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_328,c_19])).

cnf(c_25,negated_conjecture,
    ( l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_375,plain,
    ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_352,c_25])).

cnf(c_376,plain,
    ( sP1(X0,sK6,X1,k4_waybel_9(sK6,X2,X3))
    | ~ l1_waybel_0(X2,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK6) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_380,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,sK6)
    | ~ l1_waybel_0(X2,sK6)
    | sP1(X0,sK6,X1,k4_waybel_9(sK6,X2,X3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_26])).

cnf(c_381,plain,
    ( sP1(X0,sK6,X1,k4_waybel_9(sK6,X2,X3))
    | ~ l1_waybel_0(X2,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_380])).

cnf(c_2808,plain,
    ( sP1(X0_56,sK6,X0_55,k4_waybel_9(sK6,X1_55,X1_56))
    | ~ l1_waybel_0(X0_55,sK6)
    | ~ l1_waybel_0(X1_55,sK6)
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | ~ m1_subset_1(X1_56,u1_struct_0(X1_55))
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_3331,plain,
    ( sP1(X0_56,sK6,X0_55,k4_waybel_9(sK6,X1_55,X1_56)) = iProver_top
    | l1_waybel_0(X1_55,sK6) != iProver_top
    | l1_waybel_0(X0_55,sK6) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2808])).

cnf(c_7,plain,
    ( ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))
    | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2820,plain,
    ( ~ sP1(X0_56,X0_55,X1_55,k4_waybel_9(X0_55,X1_55,X0_56))
    | sP0(k4_waybel_9(X0_55,X1_55,X0_56),X1_55,X0_55,X0_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3319,plain,
    ( sP1(X0_56,X0_55,X1_55,k4_waybel_9(X0_55,X1_55,X0_56)) != iProver_top
    | sP0(k4_waybel_9(X0_55,X1_55,X0_56),X1_55,X0_55,X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2820])).

cnf(c_3883,plain,
    ( sP0(k4_waybel_9(sK6,X0_55,X0_56),X0_55,sK6,X0_56) = iProver_top
    | l1_waybel_0(X0_55,sK6) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | v2_struct_0(X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_3331,c_3319])).

cnf(c_17,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | m1_subset_1(sK5(X1,X3,X4),u1_struct_0(X1))
    | ~ r2_hidden(X4,u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2815,plain,
    ( ~ sP0(X0_55,X1_55,X2_55,X0_56)
    | m1_subset_1(sK5(X1_55,X0_56,X1_56),u1_struct_0(X1_55))
    | ~ r2_hidden(X1_56,u1_struct_0(X0_55)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3324,plain,
    ( sP0(X0_55,X1_55,X2_55,X0_56) != iProver_top
    | m1_subset_1(sK5(X1_55,X0_56,X1_56),u1_struct_0(X1_55)) = iProver_top
    | r2_hidden(X1_56,u1_struct_0(X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2815])).

cnf(c_4219,plain,
    ( l1_waybel_0(X0_55,sK6) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(sK5(X0_55,X0_56,X1_56),u1_struct_0(X0_55)) = iProver_top
    | r2_hidden(X1_56,u1_struct_0(k4_waybel_9(sK6,X0_55,X0_56))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_3883,c_3324])).

cnf(c_4778,plain,
    ( l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK5(sK7,sK8,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3329,c_4219])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,u1_struct_0(X0))
    | sK5(X1,X3,X4) = X4 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2816,plain,
    ( ~ sP0(X0_55,X1_55,X2_55,X0_56)
    | ~ r2_hidden(X1_56,u1_struct_0(X0_55))
    | sK5(X1_55,X0_56,X1_56) = X1_56 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3323,plain,
    ( sK5(X0_55,X0_56,X1_56) = X1_56
    | sP0(X1_55,X0_55,X2_55,X0_56) != iProver_top
    | r2_hidden(X1_56,u1_struct_0(X1_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2816])).

cnf(c_4120,plain,
    ( sK5(X0_55,X0_56,X1_56) = X1_56
    | l1_waybel_0(X0_55,sK6) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | r2_hidden(X1_56,u1_struct_0(k4_waybel_9(sK6,X0_55,X0_56))) != iProver_top
    | v2_struct_0(X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_3883,c_3323])).

cnf(c_4317,plain,
    ( sK5(sK7,sK8,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))) = sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3329,c_4120])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,negated_conjecture,
    ( l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2896,plain,
    ( sP1(sK8,sK6,sK7,k4_waybel_9(sK6,sK7,sK8))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ m1_subset_1(sK8,u1_struct_0(sK7))
    | v2_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2808])).

cnf(c_3582,plain,
    ( ~ sP1(X0_56,sK6,X0_55,k4_waybel_9(sK6,X0_55,X0_56))
    | sP0(k4_waybel_9(sK6,X0_55,X0_56),X0_55,sK6,X0_56) ),
    inference(instantiation,[status(thm)],[c_2820])).

cnf(c_3584,plain,
    ( ~ sP1(sK8,sK6,sK7,k4_waybel_9(sK6,sK7,sK8))
    | sP0(k4_waybel_9(sK6,sK7,sK8),sK7,sK6,sK8) ),
    inference(instantiation,[status(thm)],[c_3582])).

cnf(c_3568,plain,
    ( ~ sP0(k4_waybel_9(sK6,sK7,sK8),X0_55,X1_55,X0_56)
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8)))
    | sK5(X0_55,X0_56,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))) = sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_2816])).

cnf(c_3736,plain,
    ( ~ sP0(k4_waybel_9(sK6,sK7,sK8),sK7,sK6,sK8)
    | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8)))
    | sK5(sK7,sK8,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))) = sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3568])).

cnf(c_4379,plain,
    ( sK5(sK7,sK8,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))) = sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4317,c_24,c_23,c_22,c_310,c_2896,c_3584,c_3736])).

cnf(c_4779,plain,
    ( l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4778,c_4379])).

cnf(c_4,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_453,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_454,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(u1_waybel_0(sK6,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_2805,plain,
    ( ~ l1_waybel_0(X0_55,sK6)
    | m1_subset_1(u1_waybel_0(sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK6)))) ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_3334,plain,
    ( l1_waybel_0(X0_55,sK6) != iProver_top
    | m1_subset_1(u1_waybel_0(sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2805])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2822,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ v1_xboole_0(X1_56)
    | v1_xboole_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3317,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
    | v1_xboole_0(X1_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2822])).

cnf(c_3683,plain,
    ( l1_waybel_0(X0_55,sK6) != iProver_top
    | v1_xboole_0(u1_waybel_0(sK6,X0_55)) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3334,c_3317])).

cnf(c_3685,plain,
    ( l1_waybel_0(sK7,sK6) != iProver_top
    | v1_xboole_0(u1_waybel_0(sK6,sK7)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3683])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_316,plain,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | u1_struct_0(k4_waybel_9(sK6,sK7,sK8)) != X0
    | u1_struct_0(sK7) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_317,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) != X0
    | u1_struct_0(sK7) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_317])).

cnf(c_1005,plain,
    ( ~ m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(sK7))
    | v1_xboole_0(u1_struct_0(sK7)) ),
    inference(unflattening,[status(thm)],[c_1004])).

cnf(c_1006,plain,
    ( m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_5,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_waybel_0(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_432,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_xboole_0(u1_waybel_0(X1,X0))
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_433,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v1_xboole_0(u1_waybel_0(sK6,X0)) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_434,plain,
    ( l1_waybel_0(X0,sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v1_xboole_0(u1_waybel_0(sK6,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_436,plain,
    ( l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v1_xboole_0(u1_waybel_0(sK6,sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_31,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_30,plain,
    ( l1_waybel_0(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_27,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4779,c_3685,c_1006,c_436,c_31,c_30,c_29,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.03/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.02  
% 2.03/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.03/1.02  
% 2.03/1.02  ------  iProver source info
% 2.03/1.02  
% 2.03/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.03/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.03/1.02  git: non_committed_changes: false
% 2.03/1.02  git: last_make_outside_of_git: false
% 2.03/1.02  
% 2.03/1.02  ------ 
% 2.03/1.02  
% 2.03/1.02  ------ Input Options
% 2.03/1.02  
% 2.03/1.02  --out_options                           all
% 2.03/1.02  --tptp_safe_out                         true
% 2.03/1.02  --problem_path                          ""
% 2.03/1.02  --include_path                          ""
% 2.03/1.02  --clausifier                            res/vclausify_rel
% 2.03/1.02  --clausifier_options                    --mode clausify
% 2.03/1.02  --stdin                                 false
% 2.03/1.02  --stats_out                             all
% 2.03/1.02  
% 2.03/1.02  ------ General Options
% 2.03/1.02  
% 2.03/1.02  --fof                                   false
% 2.03/1.02  --time_out_real                         305.
% 2.03/1.02  --time_out_virtual                      -1.
% 2.03/1.02  --symbol_type_check                     false
% 2.03/1.02  --clausify_out                          false
% 2.03/1.02  --sig_cnt_out                           false
% 2.03/1.02  --trig_cnt_out                          false
% 2.03/1.02  --trig_cnt_out_tolerance                1.
% 2.03/1.02  --trig_cnt_out_sk_spl                   false
% 2.03/1.02  --abstr_cl_out                          false
% 2.03/1.02  
% 2.03/1.02  ------ Global Options
% 2.03/1.02  
% 2.03/1.02  --schedule                              default
% 2.03/1.02  --add_important_lit                     false
% 2.03/1.02  --prop_solver_per_cl                    1000
% 2.03/1.02  --min_unsat_core                        false
% 2.03/1.02  --soft_assumptions                      false
% 2.03/1.02  --soft_lemma_size                       3
% 2.03/1.02  --prop_impl_unit_size                   0
% 2.03/1.02  --prop_impl_unit                        []
% 2.03/1.02  --share_sel_clauses                     true
% 2.03/1.02  --reset_solvers                         false
% 2.03/1.02  --bc_imp_inh                            [conj_cone]
% 2.03/1.02  --conj_cone_tolerance                   3.
% 2.03/1.02  --extra_neg_conj                        none
% 2.03/1.02  --large_theory_mode                     true
% 2.03/1.02  --prolific_symb_bound                   200
% 2.03/1.02  --lt_threshold                          2000
% 2.03/1.02  --clause_weak_htbl                      true
% 2.03/1.02  --gc_record_bc_elim                     false
% 2.03/1.02  
% 2.03/1.02  ------ Preprocessing Options
% 2.03/1.02  
% 2.03/1.02  --preprocessing_flag                    true
% 2.03/1.02  --time_out_prep_mult                    0.1
% 2.03/1.02  --splitting_mode                        input
% 2.03/1.02  --splitting_grd                         true
% 2.03/1.02  --splitting_cvd                         false
% 2.03/1.02  --splitting_cvd_svl                     false
% 2.03/1.02  --splitting_nvd                         32
% 2.03/1.02  --sub_typing                            true
% 2.03/1.02  --prep_gs_sim                           true
% 2.03/1.02  --prep_unflatten                        true
% 2.03/1.02  --prep_res_sim                          true
% 2.03/1.02  --prep_upred                            true
% 2.03/1.02  --prep_sem_filter                       exhaustive
% 2.03/1.02  --prep_sem_filter_out                   false
% 2.03/1.02  --pred_elim                             true
% 2.03/1.02  --res_sim_input                         true
% 2.03/1.02  --eq_ax_congr_red                       true
% 2.03/1.02  --pure_diseq_elim                       true
% 2.03/1.02  --brand_transform                       false
% 2.03/1.02  --non_eq_to_eq                          false
% 2.03/1.02  --prep_def_merge                        true
% 2.03/1.02  --prep_def_merge_prop_impl              false
% 2.03/1.02  --prep_def_merge_mbd                    true
% 2.03/1.02  --prep_def_merge_tr_red                 false
% 2.03/1.02  --prep_def_merge_tr_cl                  false
% 2.03/1.02  --smt_preprocessing                     true
% 2.03/1.02  --smt_ac_axioms                         fast
% 2.03/1.02  --preprocessed_out                      false
% 2.03/1.02  --preprocessed_stats                    false
% 2.03/1.02  
% 2.03/1.02  ------ Abstraction refinement Options
% 2.03/1.02  
% 2.03/1.02  --abstr_ref                             []
% 2.03/1.02  --abstr_ref_prep                        false
% 2.03/1.02  --abstr_ref_until_sat                   false
% 2.03/1.02  --abstr_ref_sig_restrict                funpre
% 2.03/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/1.02  --abstr_ref_under                       []
% 2.03/1.02  
% 2.03/1.02  ------ SAT Options
% 2.03/1.02  
% 2.03/1.02  --sat_mode                              false
% 2.03/1.02  --sat_fm_restart_options                ""
% 2.03/1.02  --sat_gr_def                            false
% 2.03/1.02  --sat_epr_types                         true
% 2.03/1.02  --sat_non_cyclic_types                  false
% 2.03/1.02  --sat_finite_models                     false
% 2.03/1.02  --sat_fm_lemmas                         false
% 2.03/1.02  --sat_fm_prep                           false
% 2.03/1.02  --sat_fm_uc_incr                        true
% 2.03/1.02  --sat_out_model                         small
% 2.03/1.02  --sat_out_clauses                       false
% 2.03/1.02  
% 2.03/1.02  ------ QBF Options
% 2.03/1.02  
% 2.03/1.02  --qbf_mode                              false
% 2.03/1.02  --qbf_elim_univ                         false
% 2.03/1.02  --qbf_dom_inst                          none
% 2.03/1.02  --qbf_dom_pre_inst                      false
% 2.03/1.02  --qbf_sk_in                             false
% 2.03/1.02  --qbf_pred_elim                         true
% 2.03/1.02  --qbf_split                             512
% 2.03/1.02  
% 2.03/1.02  ------ BMC1 Options
% 2.03/1.02  
% 2.03/1.02  --bmc1_incremental                      false
% 2.03/1.02  --bmc1_axioms                           reachable_all
% 2.03/1.02  --bmc1_min_bound                        0
% 2.03/1.02  --bmc1_max_bound                        -1
% 2.03/1.02  --bmc1_max_bound_default                -1
% 2.03/1.02  --bmc1_symbol_reachability              true
% 2.03/1.02  --bmc1_property_lemmas                  false
% 2.03/1.02  --bmc1_k_induction                      false
% 2.03/1.02  --bmc1_non_equiv_states                 false
% 2.03/1.02  --bmc1_deadlock                         false
% 2.03/1.02  --bmc1_ucm                              false
% 2.03/1.02  --bmc1_add_unsat_core                   none
% 2.03/1.02  --bmc1_unsat_core_children              false
% 2.03/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/1.02  --bmc1_out_stat                         full
% 2.03/1.02  --bmc1_ground_init                      false
% 2.03/1.02  --bmc1_pre_inst_next_state              false
% 2.03/1.02  --bmc1_pre_inst_state                   false
% 2.03/1.02  --bmc1_pre_inst_reach_state             false
% 2.03/1.02  --bmc1_out_unsat_core                   false
% 2.03/1.02  --bmc1_aig_witness_out                  false
% 2.03/1.02  --bmc1_verbose                          false
% 2.03/1.02  --bmc1_dump_clauses_tptp                false
% 2.03/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.03/1.02  --bmc1_dump_file                        -
% 2.03/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.03/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.03/1.02  --bmc1_ucm_extend_mode                  1
% 2.03/1.02  --bmc1_ucm_init_mode                    2
% 2.03/1.02  --bmc1_ucm_cone_mode                    none
% 2.03/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.03/1.02  --bmc1_ucm_relax_model                  4
% 2.03/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.03/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/1.02  --bmc1_ucm_layered_model                none
% 2.03/1.02  --bmc1_ucm_max_lemma_size               10
% 2.03/1.02  
% 2.03/1.02  ------ AIG Options
% 2.03/1.02  
% 2.03/1.02  --aig_mode                              false
% 2.03/1.02  
% 2.03/1.02  ------ Instantiation Options
% 2.03/1.02  
% 2.03/1.02  --instantiation_flag                    true
% 2.03/1.02  --inst_sos_flag                         false
% 2.03/1.02  --inst_sos_phase                        true
% 2.03/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/1.02  --inst_lit_sel_side                     num_symb
% 2.03/1.02  --inst_solver_per_active                1400
% 2.03/1.02  --inst_solver_calls_frac                1.
% 2.03/1.02  --inst_passive_queue_type               priority_queues
% 2.03/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/1.02  --inst_passive_queues_freq              [25;2]
% 2.03/1.02  --inst_dismatching                      true
% 2.03/1.02  --inst_eager_unprocessed_to_passive     true
% 2.03/1.02  --inst_prop_sim_given                   true
% 2.03/1.02  --inst_prop_sim_new                     false
% 2.03/1.02  --inst_subs_new                         false
% 2.03/1.02  --inst_eq_res_simp                      false
% 2.03/1.02  --inst_subs_given                       false
% 2.03/1.02  --inst_orphan_elimination               true
% 2.03/1.02  --inst_learning_loop_flag               true
% 2.03/1.02  --inst_learning_start                   3000
% 2.03/1.02  --inst_learning_factor                  2
% 2.03/1.02  --inst_start_prop_sim_after_learn       3
% 2.03/1.02  --inst_sel_renew                        solver
% 2.03/1.02  --inst_lit_activity_flag                true
% 2.03/1.02  --inst_restr_to_given                   false
% 2.03/1.02  --inst_activity_threshold               500
% 2.03/1.02  --inst_out_proof                        true
% 2.03/1.02  
% 2.03/1.02  ------ Resolution Options
% 2.03/1.02  
% 2.03/1.02  --resolution_flag                       true
% 2.03/1.02  --res_lit_sel                           adaptive
% 2.03/1.02  --res_lit_sel_side                      none
% 2.03/1.02  --res_ordering                          kbo
% 2.03/1.02  --res_to_prop_solver                    active
% 2.03/1.02  --res_prop_simpl_new                    false
% 2.03/1.02  --res_prop_simpl_given                  true
% 2.03/1.02  --res_passive_queue_type                priority_queues
% 2.03/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/1.02  --res_passive_queues_freq               [15;5]
% 2.03/1.02  --res_forward_subs                      full
% 2.03/1.02  --res_backward_subs                     full
% 2.03/1.02  --res_forward_subs_resolution           true
% 2.03/1.02  --res_backward_subs_resolution          true
% 2.03/1.02  --res_orphan_elimination                true
% 2.03/1.02  --res_time_limit                        2.
% 2.03/1.02  --res_out_proof                         true
% 2.03/1.02  
% 2.03/1.02  ------ Superposition Options
% 2.03/1.02  
% 2.03/1.02  --superposition_flag                    true
% 2.03/1.02  --sup_passive_queue_type                priority_queues
% 2.03/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.03/1.02  --demod_completeness_check              fast
% 2.03/1.02  --demod_use_ground                      true
% 2.03/1.02  --sup_to_prop_solver                    passive
% 2.03/1.02  --sup_prop_simpl_new                    true
% 2.03/1.02  --sup_prop_simpl_given                  true
% 2.03/1.02  --sup_fun_splitting                     false
% 2.03/1.02  --sup_smt_interval                      50000
% 2.03/1.02  
% 2.03/1.02  ------ Superposition Simplification Setup
% 2.03/1.02  
% 2.03/1.02  --sup_indices_passive                   []
% 2.03/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.02  --sup_full_bw                           [BwDemod]
% 2.03/1.02  --sup_immed_triv                        [TrivRules]
% 2.03/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.02  --sup_immed_bw_main                     []
% 2.03/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.02  
% 2.03/1.02  ------ Combination Options
% 2.03/1.02  
% 2.03/1.02  --comb_res_mult                         3
% 2.03/1.02  --comb_sup_mult                         2
% 2.03/1.02  --comb_inst_mult                        10
% 2.03/1.02  
% 2.03/1.02  ------ Debug Options
% 2.03/1.02  
% 2.03/1.02  --dbg_backtrace                         false
% 2.03/1.02  --dbg_dump_prop_clauses                 false
% 2.03/1.02  --dbg_dump_prop_clauses_file            -
% 2.03/1.02  --dbg_out_stat                          false
% 2.03/1.02  ------ Parsing...
% 2.03/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.03/1.02  
% 2.03/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.03/1.02  
% 2.03/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.03/1.02  
% 2.03/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.03/1.02  ------ Proving...
% 2.03/1.02  ------ Problem Properties 
% 2.03/1.02  
% 2.03/1.02  
% 2.03/1.02  clauses                                 23
% 2.03/1.02  conjectures                             4
% 2.03/1.02  EPR                                     4
% 2.03/1.02  Horn                                    17
% 2.03/1.02  unary                                   6
% 2.03/1.02  binary                                  3
% 2.03/1.02  lits                                    69
% 2.03/1.02  lits eq                                 8
% 2.03/1.02  fd_pure                                 0
% 2.03/1.02  fd_pseudo                               0
% 2.03/1.02  fd_cond                                 0
% 2.03/1.02  fd_pseudo_cond                          1
% 2.03/1.02  AC symbols                              0
% 2.03/1.02  
% 2.03/1.02  ------ Schedule dynamic 5 is on 
% 2.03/1.02  
% 2.03/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.03/1.02  
% 2.03/1.02  
% 2.03/1.02  ------ 
% 2.03/1.02  Current options:
% 2.03/1.02  ------ 
% 2.03/1.02  
% 2.03/1.02  ------ Input Options
% 2.03/1.02  
% 2.03/1.02  --out_options                           all
% 2.03/1.02  --tptp_safe_out                         true
% 2.03/1.02  --problem_path                          ""
% 2.03/1.02  --include_path                          ""
% 2.03/1.02  --clausifier                            res/vclausify_rel
% 2.03/1.02  --clausifier_options                    --mode clausify
% 2.03/1.02  --stdin                                 false
% 2.03/1.02  --stats_out                             all
% 2.03/1.02  
% 2.03/1.02  ------ General Options
% 2.03/1.02  
% 2.03/1.02  --fof                                   false
% 2.03/1.02  --time_out_real                         305.
% 2.03/1.02  --time_out_virtual                      -1.
% 2.03/1.02  --symbol_type_check                     false
% 2.03/1.02  --clausify_out                          false
% 2.03/1.02  --sig_cnt_out                           false
% 2.03/1.02  --trig_cnt_out                          false
% 2.03/1.02  --trig_cnt_out_tolerance                1.
% 2.03/1.02  --trig_cnt_out_sk_spl                   false
% 2.03/1.02  --abstr_cl_out                          false
% 2.03/1.02  
% 2.03/1.02  ------ Global Options
% 2.03/1.02  
% 2.03/1.02  --schedule                              default
% 2.03/1.02  --add_important_lit                     false
% 2.03/1.02  --prop_solver_per_cl                    1000
% 2.03/1.02  --min_unsat_core                        false
% 2.03/1.02  --soft_assumptions                      false
% 2.03/1.02  --soft_lemma_size                       3
% 2.03/1.02  --prop_impl_unit_size                   0
% 2.03/1.02  --prop_impl_unit                        []
% 2.03/1.02  --share_sel_clauses                     true
% 2.03/1.02  --reset_solvers                         false
% 2.03/1.02  --bc_imp_inh                            [conj_cone]
% 2.03/1.02  --conj_cone_tolerance                   3.
% 2.03/1.02  --extra_neg_conj                        none
% 2.03/1.02  --large_theory_mode                     true
% 2.03/1.02  --prolific_symb_bound                   200
% 2.03/1.02  --lt_threshold                          2000
% 2.03/1.02  --clause_weak_htbl                      true
% 2.03/1.02  --gc_record_bc_elim                     false
% 2.03/1.02  
% 2.03/1.02  ------ Preprocessing Options
% 2.03/1.02  
% 2.03/1.02  --preprocessing_flag                    true
% 2.03/1.02  --time_out_prep_mult                    0.1
% 2.03/1.02  --splitting_mode                        input
% 2.03/1.02  --splitting_grd                         true
% 2.03/1.02  --splitting_cvd                         false
% 2.03/1.02  --splitting_cvd_svl                     false
% 2.03/1.02  --splitting_nvd                         32
% 2.03/1.02  --sub_typing                            true
% 2.03/1.02  --prep_gs_sim                           true
% 2.03/1.02  --prep_unflatten                        true
% 2.03/1.02  --prep_res_sim                          true
% 2.03/1.02  --prep_upred                            true
% 2.03/1.02  --prep_sem_filter                       exhaustive
% 2.03/1.02  --prep_sem_filter_out                   false
% 2.03/1.02  --pred_elim                             true
% 2.03/1.02  --res_sim_input                         true
% 2.03/1.02  --eq_ax_congr_red                       true
% 2.03/1.02  --pure_diseq_elim                       true
% 2.03/1.02  --brand_transform                       false
% 2.03/1.02  --non_eq_to_eq                          false
% 2.03/1.02  --prep_def_merge                        true
% 2.03/1.02  --prep_def_merge_prop_impl              false
% 2.03/1.02  --prep_def_merge_mbd                    true
% 2.03/1.02  --prep_def_merge_tr_red                 false
% 2.03/1.02  --prep_def_merge_tr_cl                  false
% 2.03/1.02  --smt_preprocessing                     true
% 2.03/1.02  --smt_ac_axioms                         fast
% 2.03/1.02  --preprocessed_out                      false
% 2.03/1.02  --preprocessed_stats                    false
% 2.03/1.02  
% 2.03/1.02  ------ Abstraction refinement Options
% 2.03/1.02  
% 2.03/1.02  --abstr_ref                             []
% 2.03/1.02  --abstr_ref_prep                        false
% 2.03/1.02  --abstr_ref_until_sat                   false
% 2.03/1.02  --abstr_ref_sig_restrict                funpre
% 2.03/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/1.02  --abstr_ref_under                       []
% 2.03/1.02  
% 2.03/1.02  ------ SAT Options
% 2.03/1.02  
% 2.03/1.02  --sat_mode                              false
% 2.03/1.02  --sat_fm_restart_options                ""
% 2.03/1.02  --sat_gr_def                            false
% 2.03/1.02  --sat_epr_types                         true
% 2.03/1.02  --sat_non_cyclic_types                  false
% 2.03/1.02  --sat_finite_models                     false
% 2.03/1.02  --sat_fm_lemmas                         false
% 2.03/1.02  --sat_fm_prep                           false
% 2.03/1.02  --sat_fm_uc_incr                        true
% 2.03/1.02  --sat_out_model                         small
% 2.03/1.02  --sat_out_clauses                       false
% 2.03/1.02  
% 2.03/1.02  ------ QBF Options
% 2.03/1.02  
% 2.03/1.02  --qbf_mode                              false
% 2.03/1.02  --qbf_elim_univ                         false
% 2.03/1.02  --qbf_dom_inst                          none
% 2.03/1.02  --qbf_dom_pre_inst                      false
% 2.03/1.02  --qbf_sk_in                             false
% 2.03/1.02  --qbf_pred_elim                         true
% 2.03/1.02  --qbf_split                             512
% 2.03/1.02  
% 2.03/1.02  ------ BMC1 Options
% 2.03/1.02  
% 2.03/1.02  --bmc1_incremental                      false
% 2.03/1.02  --bmc1_axioms                           reachable_all
% 2.03/1.02  --bmc1_min_bound                        0
% 2.03/1.02  --bmc1_max_bound                        -1
% 2.03/1.02  --bmc1_max_bound_default                -1
% 2.03/1.02  --bmc1_symbol_reachability              true
% 2.03/1.02  --bmc1_property_lemmas                  false
% 2.03/1.02  --bmc1_k_induction                      false
% 2.03/1.02  --bmc1_non_equiv_states                 false
% 2.03/1.02  --bmc1_deadlock                         false
% 2.03/1.02  --bmc1_ucm                              false
% 2.03/1.02  --bmc1_add_unsat_core                   none
% 2.03/1.02  --bmc1_unsat_core_children              false
% 2.03/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/1.02  --bmc1_out_stat                         full
% 2.03/1.02  --bmc1_ground_init                      false
% 2.03/1.02  --bmc1_pre_inst_next_state              false
% 2.03/1.02  --bmc1_pre_inst_state                   false
% 2.03/1.02  --bmc1_pre_inst_reach_state             false
% 2.03/1.02  --bmc1_out_unsat_core                   false
% 2.03/1.02  --bmc1_aig_witness_out                  false
% 2.03/1.02  --bmc1_verbose                          false
% 2.03/1.02  --bmc1_dump_clauses_tptp                false
% 2.03/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.03/1.02  --bmc1_dump_file                        -
% 2.03/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.03/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.03/1.02  --bmc1_ucm_extend_mode                  1
% 2.03/1.02  --bmc1_ucm_init_mode                    2
% 2.03/1.02  --bmc1_ucm_cone_mode                    none
% 2.03/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.03/1.02  --bmc1_ucm_relax_model                  4
% 2.03/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.03/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/1.02  --bmc1_ucm_layered_model                none
% 2.03/1.02  --bmc1_ucm_max_lemma_size               10
% 2.03/1.02  
% 2.03/1.02  ------ AIG Options
% 2.03/1.02  
% 2.03/1.02  --aig_mode                              false
% 2.03/1.02  
% 2.03/1.02  ------ Instantiation Options
% 2.03/1.02  
% 2.03/1.02  --instantiation_flag                    true
% 2.03/1.02  --inst_sos_flag                         false
% 2.03/1.02  --inst_sos_phase                        true
% 2.03/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/1.02  --inst_lit_sel_side                     none
% 2.03/1.02  --inst_solver_per_active                1400
% 2.03/1.02  --inst_solver_calls_frac                1.
% 2.03/1.02  --inst_passive_queue_type               priority_queues
% 2.03/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/1.02  --inst_passive_queues_freq              [25;2]
% 2.03/1.02  --inst_dismatching                      true
% 2.03/1.02  --inst_eager_unprocessed_to_passive     true
% 2.03/1.02  --inst_prop_sim_given                   true
% 2.03/1.02  --inst_prop_sim_new                     false
% 2.03/1.02  --inst_subs_new                         false
% 2.03/1.02  --inst_eq_res_simp                      false
% 2.03/1.02  --inst_subs_given                       false
% 2.03/1.02  --inst_orphan_elimination               true
% 2.03/1.02  --inst_learning_loop_flag               true
% 2.03/1.02  --inst_learning_start                   3000
% 2.03/1.02  --inst_learning_factor                  2
% 2.03/1.02  --inst_start_prop_sim_after_learn       3
% 2.03/1.02  --inst_sel_renew                        solver
% 2.03/1.02  --inst_lit_activity_flag                true
% 2.03/1.02  --inst_restr_to_given                   false
% 2.03/1.02  --inst_activity_threshold               500
% 2.03/1.02  --inst_out_proof                        true
% 2.03/1.02  
% 2.03/1.02  ------ Resolution Options
% 2.03/1.02  
% 2.03/1.02  --resolution_flag                       false
% 2.03/1.02  --res_lit_sel                           adaptive
% 2.03/1.02  --res_lit_sel_side                      none
% 2.03/1.02  --res_ordering                          kbo
% 2.03/1.02  --res_to_prop_solver                    active
% 2.03/1.02  --res_prop_simpl_new                    false
% 2.03/1.02  --res_prop_simpl_given                  true
% 2.03/1.02  --res_passive_queue_type                priority_queues
% 2.03/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/1.02  --res_passive_queues_freq               [15;5]
% 2.03/1.02  --res_forward_subs                      full
% 2.03/1.02  --res_backward_subs                     full
% 2.03/1.02  --res_forward_subs_resolution           true
% 2.03/1.02  --res_backward_subs_resolution          true
% 2.03/1.02  --res_orphan_elimination                true
% 2.03/1.02  --res_time_limit                        2.
% 2.03/1.02  --res_out_proof                         true
% 2.03/1.02  
% 2.03/1.02  ------ Superposition Options
% 2.03/1.02  
% 2.03/1.02  --superposition_flag                    true
% 2.03/1.02  --sup_passive_queue_type                priority_queues
% 2.03/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.03/1.02  --demod_completeness_check              fast
% 2.03/1.02  --demod_use_ground                      true
% 2.03/1.02  --sup_to_prop_solver                    passive
% 2.03/1.02  --sup_prop_simpl_new                    true
% 2.03/1.02  --sup_prop_simpl_given                  true
% 2.03/1.02  --sup_fun_splitting                     false
% 2.03/1.02  --sup_smt_interval                      50000
% 2.03/1.02  
% 2.03/1.02  ------ Superposition Simplification Setup
% 2.03/1.02  
% 2.03/1.02  --sup_indices_passive                   []
% 2.03/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.02  --sup_full_bw                           [BwDemod]
% 2.03/1.02  --sup_immed_triv                        [TrivRules]
% 2.03/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.02  --sup_immed_bw_main                     []
% 2.03/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.02  
% 2.03/1.02  ------ Combination Options
% 2.03/1.02  
% 2.03/1.02  --comb_res_mult                         3
% 2.03/1.02  --comb_sup_mult                         2
% 2.03/1.02  --comb_inst_mult                        10
% 2.03/1.02  
% 2.03/1.02  ------ Debug Options
% 2.03/1.02  
% 2.03/1.02  --dbg_backtrace                         false
% 2.03/1.02  --dbg_dump_prop_clauses                 false
% 2.03/1.02  --dbg_dump_prop_clauses_file            -
% 2.03/1.02  --dbg_out_stat                          false
% 2.03/1.02  
% 2.03/1.02  
% 2.03/1.02  
% 2.03/1.02  
% 2.03/1.02  ------ Proving...
% 2.03/1.02  
% 2.03/1.02  
% 2.03/1.02  % SZS status Theorem for theBenchmark.p
% 2.03/1.02  
% 2.03/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.03/1.02  
% 2.03/1.02  fof(f1,axiom,(
% 2.03/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.02  
% 2.03/1.02  fof(f10,plain,(
% 2.03/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.03/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 2.03/1.02  
% 2.03/1.02  fof(f15,plain,(
% 2.03/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.03/1.02    inference(ennf_transformation,[],[f10])).
% 2.03/1.02  
% 2.03/1.02  fof(f32,plain,(
% 2.03/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.03/1.02    introduced(choice_axiom,[])).
% 2.03/1.02  
% 2.03/1.02  fof(f33,plain,(
% 2.03/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.03/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f32])).
% 2.03/1.02  
% 2.03/1.02  fof(f47,plain,(
% 2.03/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f33])).
% 2.03/1.02  
% 2.03/1.02  fof(f8,conjecture,(
% 2.03/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 2.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.02  
% 2.03/1.02  fof(f9,negated_conjecture,(
% 2.03/1.02    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 2.03/1.02    inference(negated_conjecture,[],[f8])).
% 2.03/1.02  
% 2.03/1.02  fof(f27,plain,(
% 2.03/1.02    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 2.03/1.02    inference(ennf_transformation,[],[f9])).
% 2.03/1.02  
% 2.03/1.02  fof(f28,plain,(
% 2.03/1.02    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 2.03/1.02    inference(flattening,[],[f27])).
% 2.03/1.02  
% 2.03/1.02  fof(f45,plain,(
% 2.03/1.02    ( ! [X0,X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,sK8)),u1_struct_0(X1)) & m1_subset_1(sK8,u1_struct_0(X1)))) )),
% 2.03/1.02    introduced(choice_axiom,[])).
% 2.03/1.02  
% 2.03/1.02  fof(f44,plain,(
% 2.03/1.02    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,sK7,X2)),u1_struct_0(sK7)) & m1_subset_1(X2,u1_struct_0(sK7))) & l1_waybel_0(sK7,X0) & ~v2_struct_0(sK7))) )),
% 2.03/1.02    introduced(choice_axiom,[])).
% 2.03/1.02  
% 2.03/1.02  fof(f43,plain,(
% 2.03/1.02    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK6,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK6) & ~v2_struct_0(X1)) & l1_struct_0(sK6) & ~v2_struct_0(sK6))),
% 2.03/1.02    introduced(choice_axiom,[])).
% 2.03/1.02  
% 2.03/1.02  fof(f46,plain,(
% 2.03/1.02    ((~r1_tarski(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) & m1_subset_1(sK8,u1_struct_0(sK7))) & l1_waybel_0(sK7,sK6) & ~v2_struct_0(sK7)) & l1_struct_0(sK6) & ~v2_struct_0(sK6)),
% 2.03/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f28,f45,f44,f43])).
% 2.03/1.02  
% 2.03/1.02  fof(f73,plain,(
% 2.03/1.02    ~r1_tarski(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))),
% 2.03/1.02    inference(cnf_transformation,[],[f46])).
% 2.03/1.02  
% 2.03/1.02  fof(f6,axiom,(
% 2.03/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))))))),
% 2.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.02  
% 2.03/1.02  fof(f23,plain,(
% 2.03/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/1.02    inference(ennf_transformation,[],[f6])).
% 2.03/1.02  
% 2.03/1.02  fof(f24,plain,(
% 2.03/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/1.02    inference(flattening,[],[f23])).
% 2.03/1.02  
% 2.03/1.02  fof(f30,plain,(
% 2.03/1.02    ! [X2,X0,X1,X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> sP0(X3,X1,X0,X2)) | ~sP1(X2,X0,X1,X3))),
% 2.03/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.03/1.02  
% 2.03/1.02  fof(f29,plain,(
% 2.03/1.02    ! [X3,X1,X0,X2] : (sP0(X3,X1,X0,X2) <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))),
% 2.03/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.03/1.02  
% 2.03/1.02  fof(f31,plain,(
% 2.03/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP1(X2,X0,X1,X3) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/1.02    inference(definition_folding,[],[f24,f30,f29])).
% 2.03/1.02  
% 2.03/1.02  fof(f65,plain,(
% 2.03/1.02    ( ! [X2,X0,X3,X1] : (sP1(X2,X0,X1,X3) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f31])).
% 2.03/1.02  
% 2.03/1.02  fof(f7,axiom,(
% 2.03/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 2.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.02  
% 2.03/1.02  fof(f25,plain,(
% 2.03/1.02    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/1.02    inference(ennf_transformation,[],[f7])).
% 2.03/1.02  
% 2.03/1.02  fof(f26,plain,(
% 2.03/1.02    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/1.02    inference(flattening,[],[f25])).
% 2.03/1.02  
% 2.03/1.02  fof(f66,plain,(
% 2.03/1.02    ( ! [X2,X0,X1] : (v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f26])).
% 2.03/1.02  
% 2.03/1.02  fof(f67,plain,(
% 2.03/1.02    ( ! [X2,X0,X1] : (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f26])).
% 2.03/1.02  
% 2.03/1.02  fof(f69,plain,(
% 2.03/1.02    l1_struct_0(sK6)),
% 2.03/1.02    inference(cnf_transformation,[],[f46])).
% 2.03/1.02  
% 2.03/1.02  fof(f68,plain,(
% 2.03/1.02    ~v2_struct_0(sK6)),
% 2.03/1.02    inference(cnf_transformation,[],[f46])).
% 2.03/1.02  
% 2.03/1.02  fof(f34,plain,(
% 2.03/1.02    ! [X2,X0,X1,X3] : (((k4_waybel_9(X0,X1,X2) = X3 | ~sP0(X3,X1,X0,X2)) & (sP0(X3,X1,X0,X2) | k4_waybel_9(X0,X1,X2) != X3)) | ~sP1(X2,X0,X1,X3))),
% 2.03/1.02    inference(nnf_transformation,[],[f30])).
% 2.03/1.02  
% 2.03/1.02  fof(f35,plain,(
% 2.03/1.02    ! [X0,X1,X2,X3] : (((k4_waybel_9(X1,X2,X0) = X3 | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | k4_waybel_9(X1,X2,X0) != X3)) | ~sP1(X0,X1,X2,X3))),
% 2.03/1.02    inference(rectify,[],[f34])).
% 2.03/1.02  
% 2.03/1.02  fof(f53,plain,(
% 2.03/1.02    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0) | k4_waybel_9(X1,X2,X0) != X3 | ~sP1(X0,X1,X2,X3)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f35])).
% 2.03/1.02  
% 2.03/1.02  fof(f74,plain,(
% 2.03/1.02    ( ! [X2,X0,X1] : (sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) | ~sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))) )),
% 2.03/1.02    inference(equality_resolution,[],[f53])).
% 2.03/1.02  
% 2.03/1.02  fof(f36,plain,(
% 2.03/1.02    ! [X3,X1,X0,X2] : ((sP0(X3,X1,X0,X2) | (u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3)))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))))) | ~sP0(X3,X1,X0,X2)))),
% 2.03/1.02    inference(nnf_transformation,[],[f29])).
% 2.03/1.02  
% 2.03/1.02  fof(f37,plain,(
% 2.03/1.02    ! [X3,X1,X0,X2] : ((sP0(X3,X1,X0,X2) | u1_waybel_0(X0,X3) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) | ~r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X3))))) & ((u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : ((r2_hidden(X4,u1_struct_0(X3)) | ! [X5] : (~r1_orders_2(X1,X2,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & (? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X3))))) | ~sP0(X3,X1,X0,X2)))),
% 2.03/1.02    inference(flattening,[],[f36])).
% 2.03/1.02  
% 2.03/1.02  fof(f38,plain,(
% 2.03/1.02    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) | ~r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) | ? [X4] : ((! [X5] : (~r1_orders_2(X1,X3,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X0))) & (? [X6] : (r1_orders_2(X1,X3,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X0))))) & ((u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) & ! [X7] : ((r2_hidden(X7,u1_struct_0(X0)) | ! [X8] : (~r1_orders_2(X1,X3,X8) | X7 != X8 | ~m1_subset_1(X8,u1_struct_0(X1)))) & (? [X9] : (r1_orders_2(X1,X3,X9) & X7 = X9 & m1_subset_1(X9,u1_struct_0(X1))) | ~r2_hidden(X7,u1_struct_0(X0))))) | ~sP0(X0,X1,X2,X3)))),
% 2.03/1.02    inference(rectify,[],[f37])).
% 2.03/1.02  
% 2.03/1.02  fof(f41,plain,(
% 2.03/1.02    ! [X7,X3,X1] : (? [X9] : (r1_orders_2(X1,X3,X9) & X7 = X9 & m1_subset_1(X9,u1_struct_0(X1))) => (r1_orders_2(X1,X3,sK5(X1,X3,X7)) & sK5(X1,X3,X7) = X7 & m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1))))),
% 2.03/1.02    introduced(choice_axiom,[])).
% 2.03/1.02  
% 2.03/1.02  fof(f40,plain,(
% 2.03/1.02    ( ! [X4] : (! [X3,X1,X0] : (? [X6] : (r1_orders_2(X1,X3,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) => (r1_orders_2(X1,X3,sK4(X0,X1,X3)) & sK4(X0,X1,X3) = X4 & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X1))))) )),
% 2.03/1.02    introduced(choice_axiom,[])).
% 2.03/1.02  
% 2.03/1.02  fof(f39,plain,(
% 2.03/1.02    ! [X3,X1,X0] : (? [X4] : ((! [X5] : (~r1_orders_2(X1,X3,X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X4,u1_struct_0(X0))) & (? [X6] : (r1_orders_2(X1,X3,X6) & X4 = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(X4,u1_struct_0(X0)))) => ((! [X5] : (~r1_orders_2(X1,X3,X5) | sK3(X0,X1,X3) != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0))) & (? [X6] : (r1_orders_2(X1,X3,X6) & sK3(X0,X1,X3) = X6 & m1_subset_1(X6,u1_struct_0(X1))) | r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0)))))),
% 2.03/1.02    introduced(choice_axiom,[])).
% 2.03/1.02  
% 2.03/1.02  fof(f42,plain,(
% 2.03/1.02    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | u1_waybel_0(X2,X0) != k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) | ~r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) | ((! [X5] : (~r1_orders_2(X1,X3,X5) | sK3(X0,X1,X3) != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0))) & ((r1_orders_2(X1,X3,sK4(X0,X1,X3)) & sK3(X0,X1,X3) = sK4(X0,X1,X3) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X1))) | r2_hidden(sK3(X0,X1,X3),u1_struct_0(X0))))) & ((u1_waybel_0(X2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X0)) & r2_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0),k1_toler_1(u1_orders_2(X1),u1_struct_0(X0))) & ! [X7] : ((r2_hidden(X7,u1_struct_0(X0)) | ! [X8] : (~r1_orders_2(X1,X3,X8) | X7 != X8 | ~m1_subset_1(X8,u1_struct_0(X1)))) & ((r1_orders_2(X1,X3,sK5(X1,X3,X7)) & sK5(X1,X3,X7) = X7 & m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1))) | ~r2_hidden(X7,u1_struct_0(X0))))) | ~sP0(X0,X1,X2,X3)))),
% 2.03/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f41,f40,f39])).
% 2.03/1.02  
% 2.03/1.02  fof(f55,plain,(
% 2.03/1.02    ( ! [X2,X0,X7,X3,X1] : (m1_subset_1(sK5(X1,X3,X7),u1_struct_0(X1)) | ~r2_hidden(X7,u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f42])).
% 2.03/1.02  
% 2.03/1.02  fof(f56,plain,(
% 2.03/1.02    ( ! [X2,X0,X7,X3,X1] : (sK5(X1,X3,X7) = X7 | ~r2_hidden(X7,u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f42])).
% 2.03/1.02  
% 2.03/1.02  fof(f70,plain,(
% 2.03/1.02    ~v2_struct_0(sK7)),
% 2.03/1.02    inference(cnf_transformation,[],[f46])).
% 2.03/1.02  
% 2.03/1.02  fof(f71,plain,(
% 2.03/1.02    l1_waybel_0(sK7,sK6)),
% 2.03/1.02    inference(cnf_transformation,[],[f46])).
% 2.03/1.02  
% 2.03/1.02  fof(f72,plain,(
% 2.03/1.02    m1_subset_1(sK8,u1_struct_0(sK7))),
% 2.03/1.02    inference(cnf_transformation,[],[f46])).
% 2.03/1.02  
% 2.03/1.02  fof(f4,axiom,(
% 2.03/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 2.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.02  
% 2.03/1.02  fof(f11,plain,(
% 2.03/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 2.03/1.02    inference(pure_predicate_removal,[],[f4])).
% 2.03/1.02  
% 2.03/1.02  fof(f14,plain,(
% 2.03/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 2.03/1.02    inference(pure_predicate_removal,[],[f11])).
% 2.03/1.02  
% 2.03/1.02  fof(f19,plain,(
% 2.03/1.02    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 2.03/1.02    inference(ennf_transformation,[],[f14])).
% 2.03/1.02  
% 2.03/1.02  fof(f20,plain,(
% 2.03/1.02    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 2.03/1.02    inference(flattening,[],[f19])).
% 2.03/1.02  
% 2.03/1.02  fof(f51,plain,(
% 2.03/1.02    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f20])).
% 2.03/1.02  
% 2.03/1.02  fof(f3,axiom,(
% 2.03/1.02    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.02  
% 2.03/1.02  fof(f18,plain,(
% 2.03/1.02    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.03/1.02    inference(ennf_transformation,[],[f3])).
% 2.03/1.02  
% 2.03/1.02  fof(f50,plain,(
% 2.03/1.02    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f18])).
% 2.03/1.02  
% 2.03/1.02  fof(f2,axiom,(
% 2.03/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.02  
% 2.03/1.02  fof(f16,plain,(
% 2.03/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.03/1.02    inference(ennf_transformation,[],[f2])).
% 2.03/1.02  
% 2.03/1.02  fof(f17,plain,(
% 2.03/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.03/1.02    inference(flattening,[],[f16])).
% 2.03/1.02  
% 2.03/1.02  fof(f49,plain,(
% 2.03/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f17])).
% 2.03/1.02  
% 2.03/1.02  fof(f48,plain,(
% 2.03/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f33])).
% 2.03/1.02  
% 2.03/1.02  fof(f5,axiom,(
% 2.03/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & ~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 2.03/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/1.02  
% 2.03/1.02  fof(f12,plain,(
% 2.03/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 2.03/1.02    inference(pure_predicate_removal,[],[f5])).
% 2.03/1.02  
% 2.03/1.02  fof(f13,plain,(
% 2.03/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_waybel_0(X0,X1)))),
% 2.03/1.02    inference(pure_predicate_removal,[],[f12])).
% 2.03/1.02  
% 2.03/1.02  fof(f21,plain,(
% 2.03/1.02    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/1.02    inference(ennf_transformation,[],[f13])).
% 2.03/1.02  
% 2.03/1.02  fof(f22,plain,(
% 2.03/1.02    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/1.02    inference(flattening,[],[f21])).
% 2.03/1.02  
% 2.03/1.02  fof(f52,plain,(
% 2.03/1.02    ( ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/1.02    inference(cnf_transformation,[],[f22])).
% 2.03/1.02  
% 2.03/1.02  cnf(c_1,plain,
% 2.03/1.02      ( r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.03/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_21,negated_conjecture,
% 2.03/1.02      ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) ),
% 2.03/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_309,plain,
% 2.03/1.02      ( r2_hidden(sK2(X0,X1),X0)
% 2.03/1.02      | u1_struct_0(k4_waybel_9(sK6,sK7,sK8)) != X0
% 2.03/1.02      | u1_struct_0(sK7) != X1 ),
% 2.03/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_21]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_310,plain,
% 2.03/1.02      ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8))) ),
% 2.03/1.02      inference(unflattening,[status(thm)],[c_309]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_2810,plain,
% 2.03/1.02      ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8))) ),
% 2.03/1.02      inference(subtyping,[status(esa)],[c_310]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3329,plain,
% 2.03/1.02      ( r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8))) = iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_2810]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_18,plain,
% 2.03/1.02      ( sP1(X0,X1,X2,X3)
% 2.03/1.02      | ~ v6_waybel_0(X3,X1)
% 2.03/1.02      | ~ l1_waybel_0(X2,X1)
% 2.03/1.02      | ~ l1_waybel_0(X3,X1)
% 2.03/1.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | v2_struct_0(X2)
% 2.03/1.02      | ~ l1_struct_0(X1) ),
% 2.03/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_20,plain,
% 2.03/1.02      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
% 2.03/1.02      | ~ l1_waybel_0(X1,X0)
% 2.03/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.03/1.02      | v2_struct_0(X0)
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | ~ l1_struct_0(X0) ),
% 2.03/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_327,plain,
% 2.03/1.02      ( sP1(X0,X1,X2,X3)
% 2.03/1.02      | ~ l1_waybel_0(X2,X1)
% 2.03/1.02      | ~ l1_waybel_0(X3,X1)
% 2.03/1.02      | ~ l1_waybel_0(X4,X5)
% 2.03/1.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.03/1.02      | ~ m1_subset_1(X6,u1_struct_0(X4))
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | v2_struct_0(X2)
% 2.03/1.02      | v2_struct_0(X5)
% 2.03/1.02      | v2_struct_0(X4)
% 2.03/1.02      | ~ l1_struct_0(X1)
% 2.03/1.02      | ~ l1_struct_0(X5)
% 2.03/1.02      | X5 != X1
% 2.03/1.02      | k4_waybel_9(X5,X4,X6) != X3 ),
% 2.03/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_328,plain,
% 2.03/1.02      ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
% 2.03/1.02      | ~ l1_waybel_0(X2,X1)
% 2.03/1.02      | ~ l1_waybel_0(X3,X1)
% 2.03/1.02      | ~ l1_waybel_0(k4_waybel_9(X1,X3,X4),X1)
% 2.03/1.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.03/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | v2_struct_0(X2)
% 2.03/1.02      | v2_struct_0(X3)
% 2.03/1.02      | ~ l1_struct_0(X1) ),
% 2.03/1.02      inference(unflattening,[status(thm)],[c_327]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_19,plain,
% 2.03/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.03/1.02      | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
% 2.03/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | v2_struct_0(X0)
% 2.03/1.02      | ~ l1_struct_0(X1) ),
% 2.03/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_352,plain,
% 2.03/1.02      ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
% 2.03/1.02      | ~ l1_waybel_0(X2,X1)
% 2.03/1.02      | ~ l1_waybel_0(X3,X1)
% 2.03/1.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.03/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | v2_struct_0(X2)
% 2.03/1.02      | v2_struct_0(X3)
% 2.03/1.02      | ~ l1_struct_0(X1) ),
% 2.03/1.02      inference(forward_subsumption_resolution,
% 2.03/1.02                [status(thm)],
% 2.03/1.02                [c_328,c_19]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_25,negated_conjecture,
% 2.03/1.02      ( l1_struct_0(sK6) ),
% 2.03/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_375,plain,
% 2.03/1.02      ( sP1(X0,X1,X2,k4_waybel_9(X1,X3,X4))
% 2.03/1.02      | ~ l1_waybel_0(X2,X1)
% 2.03/1.02      | ~ l1_waybel_0(X3,X1)
% 2.03/1.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.03/1.02      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | v2_struct_0(X2)
% 2.03/1.02      | v2_struct_0(X3)
% 2.03/1.02      | sK6 != X1 ),
% 2.03/1.02      inference(resolution_lifted,[status(thm)],[c_352,c_25]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_376,plain,
% 2.03/1.02      ( sP1(X0,sK6,X1,k4_waybel_9(sK6,X2,X3))
% 2.03/1.02      | ~ l1_waybel_0(X2,sK6)
% 2.03/1.02      | ~ l1_waybel_0(X1,sK6)
% 2.03/1.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.03/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | v2_struct_0(X2)
% 2.03/1.02      | v2_struct_0(sK6) ),
% 2.03/1.02      inference(unflattening,[status(thm)],[c_375]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_26,negated_conjecture,
% 2.03/1.02      ( ~ v2_struct_0(sK6) ),
% 2.03/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_380,plain,
% 2.03/1.02      ( v2_struct_0(X2)
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.03/1.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.03/1.02      | ~ l1_waybel_0(X1,sK6)
% 2.03/1.02      | ~ l1_waybel_0(X2,sK6)
% 2.03/1.02      | sP1(X0,sK6,X1,k4_waybel_9(sK6,X2,X3)) ),
% 2.03/1.02      inference(global_propositional_subsumption,
% 2.03/1.02                [status(thm)],
% 2.03/1.02                [c_376,c_26]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_381,plain,
% 2.03/1.02      ( sP1(X0,sK6,X1,k4_waybel_9(sK6,X2,X3))
% 2.03/1.02      | ~ l1_waybel_0(X2,sK6)
% 2.03/1.02      | ~ l1_waybel_0(X1,sK6)
% 2.03/1.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.03/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | v2_struct_0(X2) ),
% 2.03/1.02      inference(renaming,[status(thm)],[c_380]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_2808,plain,
% 2.03/1.02      ( sP1(X0_56,sK6,X0_55,k4_waybel_9(sK6,X1_55,X1_56))
% 2.03/1.02      | ~ l1_waybel_0(X0_55,sK6)
% 2.03/1.02      | ~ l1_waybel_0(X1_55,sK6)
% 2.03/1.02      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 2.03/1.02      | ~ m1_subset_1(X1_56,u1_struct_0(X1_55))
% 2.03/1.02      | v2_struct_0(X0_55)
% 2.03/1.02      | v2_struct_0(X1_55) ),
% 2.03/1.02      inference(subtyping,[status(esa)],[c_381]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3331,plain,
% 2.03/1.02      ( sP1(X0_56,sK6,X0_55,k4_waybel_9(sK6,X1_55,X1_56)) = iProver_top
% 2.03/1.02      | l1_waybel_0(X1_55,sK6) != iProver_top
% 2.03/1.02      | l1_waybel_0(X0_55,sK6) != iProver_top
% 2.03/1.02      | m1_subset_1(X1_56,u1_struct_0(X1_55)) != iProver_top
% 2.03/1.02      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.03/1.02      | v2_struct_0(X0_55) = iProver_top
% 2.03/1.02      | v2_struct_0(X1_55) = iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_2808]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_7,plain,
% 2.03/1.02      ( ~ sP1(X0,X1,X2,k4_waybel_9(X1,X2,X0))
% 2.03/1.02      | sP0(k4_waybel_9(X1,X2,X0),X2,X1,X0) ),
% 2.03/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_2820,plain,
% 2.03/1.02      ( ~ sP1(X0_56,X0_55,X1_55,k4_waybel_9(X0_55,X1_55,X0_56))
% 2.03/1.02      | sP0(k4_waybel_9(X0_55,X1_55,X0_56),X1_55,X0_55,X0_56) ),
% 2.03/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3319,plain,
% 2.03/1.02      ( sP1(X0_56,X0_55,X1_55,k4_waybel_9(X0_55,X1_55,X0_56)) != iProver_top
% 2.03/1.02      | sP0(k4_waybel_9(X0_55,X1_55,X0_56),X1_55,X0_55,X0_56) = iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_2820]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3883,plain,
% 2.03/1.02      ( sP0(k4_waybel_9(sK6,X0_55,X0_56),X0_55,sK6,X0_56) = iProver_top
% 2.03/1.02      | l1_waybel_0(X0_55,sK6) != iProver_top
% 2.03/1.02      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.03/1.02      | v2_struct_0(X0_55) = iProver_top ),
% 2.03/1.02      inference(superposition,[status(thm)],[c_3331,c_3319]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_17,plain,
% 2.03/1.02      ( ~ sP0(X0,X1,X2,X3)
% 2.03/1.02      | m1_subset_1(sK5(X1,X3,X4),u1_struct_0(X1))
% 2.03/1.02      | ~ r2_hidden(X4,u1_struct_0(X0)) ),
% 2.03/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_2815,plain,
% 2.03/1.02      ( ~ sP0(X0_55,X1_55,X2_55,X0_56)
% 2.03/1.02      | m1_subset_1(sK5(X1_55,X0_56,X1_56),u1_struct_0(X1_55))
% 2.03/1.02      | ~ r2_hidden(X1_56,u1_struct_0(X0_55)) ),
% 2.03/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3324,plain,
% 2.03/1.02      ( sP0(X0_55,X1_55,X2_55,X0_56) != iProver_top
% 2.03/1.02      | m1_subset_1(sK5(X1_55,X0_56,X1_56),u1_struct_0(X1_55)) = iProver_top
% 2.03/1.02      | r2_hidden(X1_56,u1_struct_0(X0_55)) != iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_2815]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_4219,plain,
% 2.03/1.02      ( l1_waybel_0(X0_55,sK6) != iProver_top
% 2.03/1.02      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.03/1.02      | m1_subset_1(sK5(X0_55,X0_56,X1_56),u1_struct_0(X0_55)) = iProver_top
% 2.03/1.02      | r2_hidden(X1_56,u1_struct_0(k4_waybel_9(sK6,X0_55,X0_56))) != iProver_top
% 2.03/1.02      | v2_struct_0(X0_55) = iProver_top ),
% 2.03/1.02      inference(superposition,[status(thm)],[c_3883,c_3324]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_4778,plain,
% 2.03/1.02      ( l1_waybel_0(sK7,sK6) != iProver_top
% 2.03/1.02      | m1_subset_1(sK5(sK7,sK8,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))),u1_struct_0(sK7)) = iProver_top
% 2.03/1.02      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
% 2.03/1.02      | v2_struct_0(sK7) = iProver_top ),
% 2.03/1.02      inference(superposition,[status(thm)],[c_3329,c_4219]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_16,plain,
% 2.03/1.02      ( ~ sP0(X0,X1,X2,X3)
% 2.03/1.02      | ~ r2_hidden(X4,u1_struct_0(X0))
% 2.03/1.02      | sK5(X1,X3,X4) = X4 ),
% 2.03/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_2816,plain,
% 2.03/1.02      ( ~ sP0(X0_55,X1_55,X2_55,X0_56)
% 2.03/1.02      | ~ r2_hidden(X1_56,u1_struct_0(X0_55))
% 2.03/1.02      | sK5(X1_55,X0_56,X1_56) = X1_56 ),
% 2.03/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3323,plain,
% 2.03/1.02      ( sK5(X0_55,X0_56,X1_56) = X1_56
% 2.03/1.02      | sP0(X1_55,X0_55,X2_55,X0_56) != iProver_top
% 2.03/1.02      | r2_hidden(X1_56,u1_struct_0(X1_55)) != iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_2816]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_4120,plain,
% 2.03/1.02      ( sK5(X0_55,X0_56,X1_56) = X1_56
% 2.03/1.02      | l1_waybel_0(X0_55,sK6) != iProver_top
% 2.03/1.02      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.03/1.02      | r2_hidden(X1_56,u1_struct_0(k4_waybel_9(sK6,X0_55,X0_56))) != iProver_top
% 2.03/1.02      | v2_struct_0(X0_55) = iProver_top ),
% 2.03/1.02      inference(superposition,[status(thm)],[c_3883,c_3323]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_4317,plain,
% 2.03/1.02      ( sK5(sK7,sK8,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))) = sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))
% 2.03/1.02      | l1_waybel_0(sK7,sK6) != iProver_top
% 2.03/1.02      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
% 2.03/1.02      | v2_struct_0(sK7) = iProver_top ),
% 2.03/1.02      inference(superposition,[status(thm)],[c_3329,c_4120]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_24,negated_conjecture,
% 2.03/1.02      ( ~ v2_struct_0(sK7) ),
% 2.03/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_23,negated_conjecture,
% 2.03/1.02      ( l1_waybel_0(sK7,sK6) ),
% 2.03/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_22,negated_conjecture,
% 2.03/1.02      ( m1_subset_1(sK8,u1_struct_0(sK7)) ),
% 2.03/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_2896,plain,
% 2.03/1.02      ( sP1(sK8,sK6,sK7,k4_waybel_9(sK6,sK7,sK8))
% 2.03/1.02      | ~ l1_waybel_0(sK7,sK6)
% 2.03/1.02      | ~ m1_subset_1(sK8,u1_struct_0(sK7))
% 2.03/1.02      | v2_struct_0(sK7) ),
% 2.03/1.02      inference(instantiation,[status(thm)],[c_2808]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3582,plain,
% 2.03/1.02      ( ~ sP1(X0_56,sK6,X0_55,k4_waybel_9(sK6,X0_55,X0_56))
% 2.03/1.02      | sP0(k4_waybel_9(sK6,X0_55,X0_56),X0_55,sK6,X0_56) ),
% 2.03/1.02      inference(instantiation,[status(thm)],[c_2820]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3584,plain,
% 2.03/1.02      ( ~ sP1(sK8,sK6,sK7,k4_waybel_9(sK6,sK7,sK8))
% 2.03/1.02      | sP0(k4_waybel_9(sK6,sK7,sK8),sK7,sK6,sK8) ),
% 2.03/1.02      inference(instantiation,[status(thm)],[c_3582]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3568,plain,
% 2.03/1.02      ( ~ sP0(k4_waybel_9(sK6,sK7,sK8),X0_55,X1_55,X0_56)
% 2.03/1.02      | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8)))
% 2.03/1.02      | sK5(X0_55,X0_56,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))) = sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) ),
% 2.03/1.02      inference(instantiation,[status(thm)],[c_2816]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3736,plain,
% 2.03/1.02      ( ~ sP0(k4_waybel_9(sK6,sK7,sK8),sK7,sK6,sK8)
% 2.03/1.02      | ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(k4_waybel_9(sK6,sK7,sK8)))
% 2.03/1.02      | sK5(sK7,sK8,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))) = sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) ),
% 2.03/1.02      inference(instantiation,[status(thm)],[c_3568]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_4379,plain,
% 2.03/1.02      ( sK5(sK7,sK8,sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7))) = sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) ),
% 2.03/1.02      inference(global_propositional_subsumption,
% 2.03/1.02                [status(thm)],
% 2.03/1.02                [c_4317,c_24,c_23,c_22,c_310,c_2896,c_3584,c_3736]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_4779,plain,
% 2.03/1.02      ( l1_waybel_0(sK7,sK6) != iProver_top
% 2.03/1.02      | m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(sK7)) = iProver_top
% 2.03/1.02      | m1_subset_1(sK8,u1_struct_0(sK7)) != iProver_top
% 2.03/1.02      | v2_struct_0(sK7) = iProver_top ),
% 2.03/1.02      inference(light_normalisation,[status(thm)],[c_4778,c_4379]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_4,plain,
% 2.03/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.03/1.02      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.03/1.02      | ~ l1_struct_0(X1) ),
% 2.03/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_453,plain,
% 2.03/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.03/1.02      | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.03/1.02      | sK6 != X1 ),
% 2.03/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_454,plain,
% 2.03/1.02      ( ~ l1_waybel_0(X0,sK6)
% 2.03/1.02      | m1_subset_1(u1_waybel_0(sK6,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK6)))) ),
% 2.03/1.02      inference(unflattening,[status(thm)],[c_453]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_2805,plain,
% 2.03/1.02      ( ~ l1_waybel_0(X0_55,sK6)
% 2.03/1.02      | m1_subset_1(u1_waybel_0(sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK6)))) ),
% 2.03/1.02      inference(subtyping,[status(esa)],[c_454]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3334,plain,
% 2.03/1.02      ( l1_waybel_0(X0_55,sK6) != iProver_top
% 2.03/1.02      | m1_subset_1(u1_waybel_0(sK6,X0_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK6)))) = iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_2805]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3,plain,
% 2.03/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.03/1.02      | ~ v1_xboole_0(X1)
% 2.03/1.02      | v1_xboole_0(X0) ),
% 2.03/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_2822,plain,
% 2.03/1.02      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 2.03/1.02      | ~ v1_xboole_0(X1_56)
% 2.03/1.02      | v1_xboole_0(X0_56) ),
% 2.03/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3317,plain,
% 2.03/1.02      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
% 2.03/1.02      | v1_xboole_0(X1_56) != iProver_top
% 2.03/1.02      | v1_xboole_0(X0_56) = iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_2822]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3683,plain,
% 2.03/1.02      ( l1_waybel_0(X0_55,sK6) != iProver_top
% 2.03/1.02      | v1_xboole_0(u1_waybel_0(sK6,X0_55)) = iProver_top
% 2.03/1.02      | v1_xboole_0(u1_struct_0(X0_55)) != iProver_top ),
% 2.03/1.02      inference(superposition,[status(thm)],[c_3334,c_3317]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_3685,plain,
% 2.03/1.02      ( l1_waybel_0(sK7,sK6) != iProver_top
% 2.03/1.02      | v1_xboole_0(u1_waybel_0(sK6,sK7)) = iProver_top
% 2.03/1.02      | v1_xboole_0(u1_struct_0(sK7)) != iProver_top ),
% 2.03/1.02      inference(instantiation,[status(thm)],[c_3683]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_2,plain,
% 2.03/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.03/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_0,plain,
% 2.03/1.02      ( ~ r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.03/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_316,plain,
% 2.03/1.02      ( ~ r2_hidden(sK2(X0,X1),X1)
% 2.03/1.02      | u1_struct_0(k4_waybel_9(sK6,sK7,sK8)) != X0
% 2.03/1.02      | u1_struct_0(sK7) != X1 ),
% 2.03/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_317,plain,
% 2.03/1.02      ( ~ r2_hidden(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(sK7)) ),
% 2.03/1.02      inference(unflattening,[status(thm)],[c_316]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_1004,plain,
% 2.03/1.02      ( ~ m1_subset_1(X0,X1)
% 2.03/1.02      | v1_xboole_0(X1)
% 2.03/1.02      | sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)) != X0
% 2.03/1.02      | u1_struct_0(sK7) != X1 ),
% 2.03/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_317]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_1005,plain,
% 2.03/1.02      ( ~ m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(sK7))
% 2.03/1.02      | v1_xboole_0(u1_struct_0(sK7)) ),
% 2.03/1.02      inference(unflattening,[status(thm)],[c_1004]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_1006,plain,
% 2.03/1.02      ( m1_subset_1(sK2(u1_struct_0(k4_waybel_9(sK6,sK7,sK8)),u1_struct_0(sK7)),u1_struct_0(sK7)) != iProver_top
% 2.03/1.02      | v1_xboole_0(u1_struct_0(sK7)) = iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_1005]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_5,plain,
% 2.03/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | v2_struct_0(X0)
% 2.03/1.02      | ~ l1_struct_0(X1)
% 2.03/1.02      | ~ v1_xboole_0(u1_waybel_0(X1,X0)) ),
% 2.03/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_432,plain,
% 2.03/1.02      ( ~ l1_waybel_0(X0,X1)
% 2.03/1.02      | v2_struct_0(X0)
% 2.03/1.02      | v2_struct_0(X1)
% 2.03/1.02      | ~ v1_xboole_0(u1_waybel_0(X1,X0))
% 2.03/1.02      | sK6 != X1 ),
% 2.03/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_433,plain,
% 2.03/1.02      ( ~ l1_waybel_0(X0,sK6)
% 2.03/1.02      | v2_struct_0(X0)
% 2.03/1.02      | v2_struct_0(sK6)
% 2.03/1.02      | ~ v1_xboole_0(u1_waybel_0(sK6,X0)) ),
% 2.03/1.02      inference(unflattening,[status(thm)],[c_432]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_434,plain,
% 2.03/1.02      ( l1_waybel_0(X0,sK6) != iProver_top
% 2.03/1.02      | v2_struct_0(X0) = iProver_top
% 2.03/1.02      | v2_struct_0(sK6) = iProver_top
% 2.03/1.02      | v1_xboole_0(u1_waybel_0(sK6,X0)) != iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_436,plain,
% 2.03/1.02      ( l1_waybel_0(sK7,sK6) != iProver_top
% 2.03/1.02      | v2_struct_0(sK7) = iProver_top
% 2.03/1.02      | v2_struct_0(sK6) = iProver_top
% 2.03/1.02      | v1_xboole_0(u1_waybel_0(sK6,sK7)) != iProver_top ),
% 2.03/1.02      inference(instantiation,[status(thm)],[c_434]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_31,plain,
% 2.03/1.02      ( m1_subset_1(sK8,u1_struct_0(sK7)) = iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_30,plain,
% 2.03/1.02      ( l1_waybel_0(sK7,sK6) = iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_29,plain,
% 2.03/1.02      ( v2_struct_0(sK7) != iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(c_27,plain,
% 2.03/1.02      ( v2_struct_0(sK6) != iProver_top ),
% 2.03/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.03/1.02  
% 2.03/1.02  cnf(contradiction,plain,
% 2.03/1.02      ( $false ),
% 2.03/1.02      inference(minisat,
% 2.03/1.02                [status(thm)],
% 2.03/1.02                [c_4779,c_3685,c_1006,c_436,c_31,c_30,c_29,c_27]) ).
% 2.03/1.02  
% 2.03/1.02  
% 2.03/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.03/1.02  
% 2.03/1.02  ------                               Statistics
% 2.03/1.02  
% 2.03/1.02  ------ General
% 2.03/1.02  
% 2.03/1.02  abstr_ref_over_cycles:                  0
% 2.03/1.02  abstr_ref_under_cycles:                 0
% 2.03/1.02  gc_basic_clause_elim:                   0
% 2.03/1.02  forced_gc_time:                         0
% 2.03/1.02  parsing_time:                           0.011
% 2.03/1.02  unif_index_cands_time:                  0.
% 2.03/1.02  unif_index_add_time:                    0.
% 2.03/1.02  orderings_time:                         0.
% 2.03/1.02  out_proof_time:                         0.011
% 2.03/1.02  total_time:                             0.156
% 2.03/1.02  num_of_symbols:                         64
% 2.03/1.02  num_of_terms:                           4002
% 2.03/1.02  
% 2.03/1.02  ------ Preprocessing
% 2.03/1.02  
% 2.03/1.02  num_of_splits:                          0
% 2.03/1.02  num_of_split_atoms:                     0
% 2.03/1.02  num_of_reused_defs:                     0
% 2.03/1.02  num_eq_ax_congr_red:                    57
% 2.03/1.02  num_of_sem_filtered_clauses:            1
% 2.03/1.02  num_of_subtypes:                        3
% 2.03/1.02  monotx_restored_types:                  1
% 2.03/1.02  sat_num_of_epr_types:                   0
% 2.03/1.02  sat_num_of_non_cyclic_types:            0
% 2.03/1.02  sat_guarded_non_collapsed_types:        1
% 2.03/1.02  num_pure_diseq_elim:                    0
% 2.03/1.02  simp_replaced_by:                       0
% 2.03/1.02  res_preprocessed:                       137
% 2.03/1.02  prep_upred:                             0
% 2.03/1.02  prep_unflattend:                        92
% 2.03/1.02  smt_new_axioms:                         0
% 2.03/1.02  pred_elim_cands:                        8
% 2.03/1.02  pred_elim:                              4
% 2.03/1.02  pred_elim_cl:                           4
% 2.03/1.02  pred_elim_cycles:                       10
% 2.03/1.02  merged_defs:                            0
% 2.03/1.02  merged_defs_ncl:                        0
% 2.03/1.02  bin_hyper_res:                          0
% 2.03/1.02  prep_cycles:                            4
% 2.03/1.02  pred_elim_time:                         0.045
% 2.03/1.02  splitting_time:                         0.
% 2.03/1.02  sem_filter_time:                        0.
% 2.03/1.02  monotx_time:                            0.001
% 2.03/1.02  subtype_inf_time:                       0.001
% 2.03/1.02  
% 2.03/1.02  ------ Problem properties
% 2.03/1.02  
% 2.03/1.02  clauses:                                23
% 2.03/1.02  conjectures:                            4
% 2.03/1.02  epr:                                    4
% 2.03/1.02  horn:                                   17
% 2.03/1.02  ground:                                 6
% 2.03/1.02  unary:                                  6
% 2.03/1.02  binary:                                 3
% 2.03/1.02  lits:                                   69
% 2.03/1.02  lits_eq:                                8
% 2.03/1.02  fd_pure:                                0
% 2.03/1.02  fd_pseudo:                              0
% 2.03/1.02  fd_cond:                                0
% 2.03/1.02  fd_pseudo_cond:                         1
% 2.03/1.02  ac_symbols:                             0
% 2.03/1.02  
% 2.03/1.02  ------ Propositional Solver
% 2.03/1.02  
% 2.03/1.02  prop_solver_calls:                      26
% 2.03/1.02  prop_fast_solver_calls:                 1452
% 2.03/1.02  smt_solver_calls:                       0
% 2.03/1.02  smt_fast_solver_calls:                  0
% 2.03/1.02  prop_num_of_clauses:                    865
% 2.03/1.02  prop_preprocess_simplified:             4833
% 2.03/1.02  prop_fo_subsumed:                       14
% 2.03/1.02  prop_solver_time:                       0.
% 2.03/1.02  smt_solver_time:                        0.
% 2.03/1.02  smt_fast_solver_time:                   0.
% 2.03/1.02  prop_fast_solver_time:                  0.
% 2.03/1.02  prop_unsat_core_time:                   0.
% 2.03/1.02  
% 2.03/1.02  ------ QBF
% 2.03/1.02  
% 2.03/1.02  qbf_q_res:                              0
% 2.03/1.02  qbf_num_tautologies:                    0
% 2.03/1.02  qbf_prep_cycles:                        0
% 2.03/1.02  
% 2.03/1.02  ------ BMC1
% 2.03/1.02  
% 2.03/1.02  bmc1_current_bound:                     -1
% 2.03/1.02  bmc1_last_solved_bound:                 -1
% 2.03/1.02  bmc1_unsat_core_size:                   -1
% 2.03/1.02  bmc1_unsat_core_parents_size:           -1
% 2.03/1.02  bmc1_merge_next_fun:                    0
% 2.03/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.03/1.02  
% 2.03/1.02  ------ Instantiation
% 2.03/1.02  
% 2.03/1.02  inst_num_of_clauses:                    255
% 2.03/1.02  inst_num_in_passive:                    8
% 2.03/1.02  inst_num_in_active:                     173
% 2.03/1.02  inst_num_in_unprocessed:                75
% 2.03/1.02  inst_num_of_loops:                      180
% 2.03/1.02  inst_num_of_learning_restarts:          0
% 2.03/1.02  inst_num_moves_active_passive:          4
% 2.03/1.02  inst_lit_activity:                      0
% 2.03/1.02  inst_lit_activity_moves:                0
% 2.03/1.02  inst_num_tautologies:                   0
% 2.03/1.02  inst_num_prop_implied:                  0
% 2.03/1.02  inst_num_existing_simplified:           0
% 2.03/1.02  inst_num_eq_res_simplified:             0
% 2.03/1.02  inst_num_child_elim:                    0
% 2.03/1.02  inst_num_of_dismatching_blockings:      66
% 2.03/1.02  inst_num_of_non_proper_insts:           224
% 2.03/1.02  inst_num_of_duplicates:                 0
% 2.03/1.02  inst_inst_num_from_inst_to_res:         0
% 2.03/1.02  inst_dismatching_checking_time:         0.
% 2.03/1.02  
% 2.03/1.02  ------ Resolution
% 2.03/1.02  
% 2.03/1.02  res_num_of_clauses:                     0
% 2.03/1.02  res_num_in_passive:                     0
% 2.03/1.02  res_num_in_active:                      0
% 2.03/1.02  res_num_of_loops:                       141
% 2.03/1.02  res_forward_subset_subsumed:            31
% 2.03/1.02  res_backward_subset_subsumed:           2
% 2.03/1.02  res_forward_subsumed:                   0
% 2.03/1.02  res_backward_subsumed:                  0
% 2.03/1.02  res_forward_subsumption_resolution:     2
% 2.03/1.02  res_backward_subsumption_resolution:    0
% 2.03/1.02  res_clause_to_clause_subsumption:       148
% 2.03/1.02  res_orphan_elimination:                 0
% 2.03/1.02  res_tautology_del:                      48
% 2.03/1.02  res_num_eq_res_simplified:              0
% 2.03/1.02  res_num_sel_changes:                    0
% 2.03/1.02  res_moves_from_active_to_pass:          0
% 2.03/1.02  
% 2.03/1.02  ------ Superposition
% 2.03/1.02  
% 2.03/1.02  sup_time_total:                         0.
% 2.03/1.02  sup_time_generating:                    0.
% 2.03/1.02  sup_time_sim_full:                      0.
% 2.03/1.02  sup_time_sim_immed:                     0.
% 2.03/1.02  
% 2.03/1.02  sup_num_of_clauses:                     42
% 2.03/1.02  sup_num_in_active:                      35
% 2.03/1.02  sup_num_in_passive:                     7
% 2.03/1.02  sup_num_of_loops:                       34
% 2.03/1.02  sup_fw_superposition:                   15
% 2.03/1.02  sup_bw_superposition:                   4
% 2.03/1.02  sup_immediate_simplified:               2
% 2.03/1.02  sup_given_eliminated:                   0
% 2.03/1.02  comparisons_done:                       0
% 2.03/1.02  comparisons_avoided:                    0
% 2.03/1.02  
% 2.03/1.02  ------ Simplifications
% 2.03/1.02  
% 2.03/1.02  
% 2.03/1.02  sim_fw_subset_subsumed:                 0
% 2.03/1.02  sim_bw_subset_subsumed:                 0
% 2.03/1.02  sim_fw_subsumed:                        0
% 2.03/1.02  sim_bw_subsumed:                        0
% 2.03/1.02  sim_fw_subsumption_res:                 0
% 2.03/1.02  sim_bw_subsumption_res:                 0
% 2.03/1.02  sim_tautology_del:                      0
% 2.03/1.02  sim_eq_tautology_del:                   1
% 2.03/1.02  sim_eq_res_simp:                        0
% 2.03/1.02  sim_fw_demodulated:                     0
% 2.03/1.02  sim_bw_demodulated:                     0
% 2.03/1.02  sim_light_normalised:                   2
% 2.03/1.02  sim_joinable_taut:                      0
% 2.03/1.02  sim_joinable_simp:                      0
% 2.03/1.02  sim_ac_normalised:                      0
% 2.03/1.02  sim_smt_subsumption:                    0
% 2.03/1.02  
%------------------------------------------------------------------------------
