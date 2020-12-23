%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:22 EST 2020

% Result     : Theorem 1.29s
% Output     : CNFRefutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 383 expanded)
%              Number of clauses        :   52 (  91 expanded)
%              Number of leaves         :   21 (  99 expanded)
%              Depth                    :   19
%              Number of atoms          :  440 (1585 expanded)
%              Number of equality atoms :  143 ( 206 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( r2_hidden(sK4,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1)))
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f45,f44])).

fof(f81,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f83])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f84])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f85])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f86])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f87])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f74,f88])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f33,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f18,f34,f33])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f67])).

fof(f40,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f41])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f66])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f88])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2047,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_19,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_18,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_309,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_19,c_18])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_401,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_309,c_28])).

cnf(c_402,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_24,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,plain,
    ( ~ l1_orders_2(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_46,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_404,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_28,c_24,c_43,c_46])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_404])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK3),X0) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_2045,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK3),X0)
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_2251,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(u1_struct_0(sK3),sK4) ),
    inference(superposition,[status(thm)],[c_2047,c_2045])).

cnf(c_14,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2051,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2730,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_2051])).

cnf(c_4,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2061,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2063,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3161,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2061,c_2063])).

cnf(c_4951,plain,
    ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_3161])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2048,plain,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2050,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2850,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(X0)) = iProver_top
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_2050])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k1_orders_2(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k1_orders_2(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK3,X1))
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_27,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_26,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_28,c_27,c_26,c_24])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | ~ r2_hidden(X1,k1_orders_2(sK3,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_376,c_17])).

cnf(c_2046,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_2882,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
    | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_2046])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | u1_struct_0(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_404])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_2206,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_2207,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2206])).

cnf(c_3931,plain,
    ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
    | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2882,c_34,c_2207])).

cnf(c_3932,plain,
    ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
    | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3931])).

cnf(c_3940,plain,
    ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_3932])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4951,c_3940])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.29/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.29/1.04  
% 1.29/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.29/1.04  
% 1.29/1.04  ------  iProver source info
% 1.29/1.04  
% 1.29/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.29/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.29/1.04  git: non_committed_changes: false
% 1.29/1.04  git: last_make_outside_of_git: false
% 1.29/1.04  
% 1.29/1.04  ------ 
% 1.29/1.04  
% 1.29/1.04  ------ Input Options
% 1.29/1.04  
% 1.29/1.04  --out_options                           all
% 1.29/1.04  --tptp_safe_out                         true
% 1.29/1.04  --problem_path                          ""
% 1.29/1.04  --include_path                          ""
% 1.29/1.04  --clausifier                            res/vclausify_rel
% 1.29/1.04  --clausifier_options                    --mode clausify
% 1.29/1.04  --stdin                                 false
% 1.29/1.04  --stats_out                             all
% 1.29/1.04  
% 1.29/1.04  ------ General Options
% 1.29/1.04  
% 1.29/1.04  --fof                                   false
% 1.29/1.04  --time_out_real                         305.
% 1.29/1.04  --time_out_virtual                      -1.
% 1.29/1.04  --symbol_type_check                     false
% 1.29/1.04  --clausify_out                          false
% 1.29/1.04  --sig_cnt_out                           false
% 1.29/1.04  --trig_cnt_out                          false
% 1.29/1.04  --trig_cnt_out_tolerance                1.
% 1.29/1.04  --trig_cnt_out_sk_spl                   false
% 1.29/1.04  --abstr_cl_out                          false
% 1.29/1.04  
% 1.29/1.04  ------ Global Options
% 1.29/1.04  
% 1.29/1.04  --schedule                              default
% 1.29/1.04  --add_important_lit                     false
% 1.29/1.04  --prop_solver_per_cl                    1000
% 1.29/1.04  --min_unsat_core                        false
% 1.29/1.04  --soft_assumptions                      false
% 1.29/1.04  --soft_lemma_size                       3
% 1.29/1.04  --prop_impl_unit_size                   0
% 1.29/1.04  --prop_impl_unit                        []
% 1.29/1.04  --share_sel_clauses                     true
% 1.29/1.04  --reset_solvers                         false
% 1.29/1.04  --bc_imp_inh                            [conj_cone]
% 1.29/1.04  --conj_cone_tolerance                   3.
% 1.29/1.04  --extra_neg_conj                        none
% 1.29/1.04  --large_theory_mode                     true
% 1.29/1.04  --prolific_symb_bound                   200
% 1.29/1.04  --lt_threshold                          2000
% 1.29/1.04  --clause_weak_htbl                      true
% 1.29/1.04  --gc_record_bc_elim                     false
% 1.29/1.04  
% 1.29/1.04  ------ Preprocessing Options
% 1.29/1.04  
% 1.29/1.04  --preprocessing_flag                    true
% 1.29/1.04  --time_out_prep_mult                    0.1
% 1.29/1.04  --splitting_mode                        input
% 1.29/1.04  --splitting_grd                         true
% 1.29/1.04  --splitting_cvd                         false
% 1.29/1.04  --splitting_cvd_svl                     false
% 1.29/1.04  --splitting_nvd                         32
% 1.29/1.04  --sub_typing                            true
% 1.29/1.04  --prep_gs_sim                           true
% 1.29/1.04  --prep_unflatten                        true
% 1.29/1.04  --prep_res_sim                          true
% 1.29/1.04  --prep_upred                            true
% 1.29/1.04  --prep_sem_filter                       exhaustive
% 1.29/1.04  --prep_sem_filter_out                   false
% 1.29/1.04  --pred_elim                             true
% 1.29/1.04  --res_sim_input                         true
% 1.29/1.04  --eq_ax_congr_red                       true
% 1.29/1.04  --pure_diseq_elim                       true
% 1.29/1.04  --brand_transform                       false
% 1.29/1.04  --non_eq_to_eq                          false
% 1.29/1.04  --prep_def_merge                        true
% 1.29/1.04  --prep_def_merge_prop_impl              false
% 1.29/1.04  --prep_def_merge_mbd                    true
% 1.29/1.04  --prep_def_merge_tr_red                 false
% 1.29/1.04  --prep_def_merge_tr_cl                  false
% 1.29/1.04  --smt_preprocessing                     true
% 1.29/1.04  --smt_ac_axioms                         fast
% 1.29/1.04  --preprocessed_out                      false
% 1.29/1.04  --preprocessed_stats                    false
% 1.29/1.04  
% 1.29/1.04  ------ Abstraction refinement Options
% 1.29/1.04  
% 1.29/1.04  --abstr_ref                             []
% 1.29/1.04  --abstr_ref_prep                        false
% 1.29/1.04  --abstr_ref_until_sat                   false
% 1.29/1.04  --abstr_ref_sig_restrict                funpre
% 1.29/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.29/1.04  --abstr_ref_under                       []
% 1.29/1.04  
% 1.29/1.04  ------ SAT Options
% 1.29/1.04  
% 1.29/1.04  --sat_mode                              false
% 1.29/1.04  --sat_fm_restart_options                ""
% 1.29/1.04  --sat_gr_def                            false
% 1.29/1.04  --sat_epr_types                         true
% 1.29/1.04  --sat_non_cyclic_types                  false
% 1.29/1.04  --sat_finite_models                     false
% 1.29/1.04  --sat_fm_lemmas                         false
% 1.29/1.04  --sat_fm_prep                           false
% 1.29/1.04  --sat_fm_uc_incr                        true
% 1.29/1.04  --sat_out_model                         small
% 1.29/1.04  --sat_out_clauses                       false
% 1.29/1.04  
% 1.29/1.04  ------ QBF Options
% 1.29/1.04  
% 1.29/1.04  --qbf_mode                              false
% 1.29/1.04  --qbf_elim_univ                         false
% 1.29/1.04  --qbf_dom_inst                          none
% 1.29/1.04  --qbf_dom_pre_inst                      false
% 1.29/1.04  --qbf_sk_in                             false
% 1.29/1.04  --qbf_pred_elim                         true
% 1.29/1.04  --qbf_split                             512
% 1.29/1.04  
% 1.29/1.04  ------ BMC1 Options
% 1.29/1.04  
% 1.29/1.04  --bmc1_incremental                      false
% 1.29/1.04  --bmc1_axioms                           reachable_all
% 1.29/1.04  --bmc1_min_bound                        0
% 1.29/1.04  --bmc1_max_bound                        -1
% 1.29/1.04  --bmc1_max_bound_default                -1
% 1.29/1.04  --bmc1_symbol_reachability              true
% 1.29/1.04  --bmc1_property_lemmas                  false
% 1.29/1.04  --bmc1_k_induction                      false
% 1.29/1.04  --bmc1_non_equiv_states                 false
% 1.29/1.04  --bmc1_deadlock                         false
% 1.29/1.04  --bmc1_ucm                              false
% 1.29/1.04  --bmc1_add_unsat_core                   none
% 1.29/1.04  --bmc1_unsat_core_children              false
% 1.29/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.29/1.04  --bmc1_out_stat                         full
% 1.29/1.04  --bmc1_ground_init                      false
% 1.29/1.04  --bmc1_pre_inst_next_state              false
% 1.29/1.04  --bmc1_pre_inst_state                   false
% 1.29/1.04  --bmc1_pre_inst_reach_state             false
% 1.29/1.04  --bmc1_out_unsat_core                   false
% 1.29/1.04  --bmc1_aig_witness_out                  false
% 1.29/1.04  --bmc1_verbose                          false
% 1.29/1.04  --bmc1_dump_clauses_tptp                false
% 1.29/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.29/1.04  --bmc1_dump_file                        -
% 1.29/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.29/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.29/1.04  --bmc1_ucm_extend_mode                  1
% 1.29/1.04  --bmc1_ucm_init_mode                    2
% 1.29/1.04  --bmc1_ucm_cone_mode                    none
% 1.29/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.29/1.04  --bmc1_ucm_relax_model                  4
% 1.29/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.29/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.29/1.04  --bmc1_ucm_layered_model                none
% 1.29/1.04  --bmc1_ucm_max_lemma_size               10
% 1.29/1.04  
% 1.29/1.04  ------ AIG Options
% 1.29/1.04  
% 1.29/1.04  --aig_mode                              false
% 1.29/1.04  
% 1.29/1.04  ------ Instantiation Options
% 1.29/1.04  
% 1.29/1.04  --instantiation_flag                    true
% 1.29/1.04  --inst_sos_flag                         false
% 1.29/1.04  --inst_sos_phase                        true
% 1.29/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.29/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.29/1.04  --inst_lit_sel_side                     num_symb
% 1.29/1.04  --inst_solver_per_active                1400
% 1.29/1.04  --inst_solver_calls_frac                1.
% 1.29/1.04  --inst_passive_queue_type               priority_queues
% 1.29/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.29/1.04  --inst_passive_queues_freq              [25;2]
% 1.29/1.04  --inst_dismatching                      true
% 1.29/1.04  --inst_eager_unprocessed_to_passive     true
% 1.29/1.04  --inst_prop_sim_given                   true
% 1.29/1.04  --inst_prop_sim_new                     false
% 1.29/1.04  --inst_subs_new                         false
% 1.29/1.04  --inst_eq_res_simp                      false
% 1.29/1.04  --inst_subs_given                       false
% 1.29/1.04  --inst_orphan_elimination               true
% 1.29/1.04  --inst_learning_loop_flag               true
% 1.29/1.04  --inst_learning_start                   3000
% 1.29/1.04  --inst_learning_factor                  2
% 1.29/1.04  --inst_start_prop_sim_after_learn       3
% 1.29/1.04  --inst_sel_renew                        solver
% 1.29/1.04  --inst_lit_activity_flag                true
% 1.29/1.04  --inst_restr_to_given                   false
% 1.29/1.04  --inst_activity_threshold               500
% 1.29/1.04  --inst_out_proof                        true
% 1.29/1.04  
% 1.29/1.04  ------ Resolution Options
% 1.29/1.04  
% 1.29/1.04  --resolution_flag                       true
% 1.29/1.04  --res_lit_sel                           adaptive
% 1.29/1.04  --res_lit_sel_side                      none
% 1.29/1.04  --res_ordering                          kbo
% 1.29/1.04  --res_to_prop_solver                    active
% 1.29/1.04  --res_prop_simpl_new                    false
% 1.29/1.04  --res_prop_simpl_given                  true
% 1.29/1.04  --res_passive_queue_type                priority_queues
% 1.29/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.29/1.04  --res_passive_queues_freq               [15;5]
% 1.29/1.04  --res_forward_subs                      full
% 1.29/1.04  --res_backward_subs                     full
% 1.29/1.04  --res_forward_subs_resolution           true
% 1.29/1.04  --res_backward_subs_resolution          true
% 1.29/1.04  --res_orphan_elimination                true
% 1.29/1.04  --res_time_limit                        2.
% 1.29/1.04  --res_out_proof                         true
% 1.29/1.04  
% 1.29/1.04  ------ Superposition Options
% 1.29/1.04  
% 1.29/1.04  --superposition_flag                    true
% 1.29/1.04  --sup_passive_queue_type                priority_queues
% 1.29/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.29/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.29/1.04  --demod_completeness_check              fast
% 1.29/1.04  --demod_use_ground                      true
% 1.29/1.04  --sup_to_prop_solver                    passive
% 1.29/1.04  --sup_prop_simpl_new                    true
% 1.29/1.04  --sup_prop_simpl_given                  true
% 1.29/1.04  --sup_fun_splitting                     false
% 1.29/1.04  --sup_smt_interval                      50000
% 1.29/1.04  
% 1.29/1.04  ------ Superposition Simplification Setup
% 1.29/1.04  
% 1.29/1.04  --sup_indices_passive                   []
% 1.29/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.29/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.04  --sup_full_bw                           [BwDemod]
% 1.29/1.04  --sup_immed_triv                        [TrivRules]
% 1.29/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.29/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.04  --sup_immed_bw_main                     []
% 1.29/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.29/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.04  
% 1.29/1.04  ------ Combination Options
% 1.29/1.04  
% 1.29/1.04  --comb_res_mult                         3
% 1.29/1.04  --comb_sup_mult                         2
% 1.29/1.04  --comb_inst_mult                        10
% 1.29/1.04  
% 1.29/1.04  ------ Debug Options
% 1.29/1.04  
% 1.29/1.04  --dbg_backtrace                         false
% 1.29/1.04  --dbg_dump_prop_clauses                 false
% 1.29/1.04  --dbg_dump_prop_clauses_file            -
% 1.29/1.04  --dbg_out_stat                          false
% 1.29/1.04  ------ Parsing...
% 1.29/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.29/1.04  
% 1.29/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.29/1.04  
% 1.29/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.29/1.04  
% 1.29/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.29/1.04  ------ Proving...
% 1.29/1.04  ------ Problem Properties 
% 1.29/1.04  
% 1.29/1.04  
% 1.29/1.04  clauses                                 22
% 1.29/1.04  conjectures                             2
% 1.29/1.04  EPR                                     11
% 1.29/1.04  Horn                                    20
% 1.29/1.04  unary                                   11
% 1.29/1.04  binary                                  4
% 1.29/1.04  lits                                    46
% 1.29/1.04  lits eq                                 10
% 1.29/1.04  fd_pure                                 0
% 1.29/1.04  fd_pseudo                               0
% 1.29/1.04  fd_cond                                 0
% 1.29/1.04  fd_pseudo_cond                          2
% 1.29/1.04  AC symbols                              0
% 1.29/1.04  
% 1.29/1.04  ------ Schedule dynamic 5 is on 
% 1.29/1.04  
% 1.29/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.29/1.04  
% 1.29/1.04  
% 1.29/1.04  ------ 
% 1.29/1.04  Current options:
% 1.29/1.04  ------ 
% 1.29/1.04  
% 1.29/1.04  ------ Input Options
% 1.29/1.04  
% 1.29/1.04  --out_options                           all
% 1.29/1.04  --tptp_safe_out                         true
% 1.29/1.04  --problem_path                          ""
% 1.29/1.04  --include_path                          ""
% 1.29/1.04  --clausifier                            res/vclausify_rel
% 1.29/1.04  --clausifier_options                    --mode clausify
% 1.29/1.04  --stdin                                 false
% 1.29/1.04  --stats_out                             all
% 1.29/1.04  
% 1.29/1.04  ------ General Options
% 1.29/1.04  
% 1.29/1.04  --fof                                   false
% 1.29/1.04  --time_out_real                         305.
% 1.29/1.04  --time_out_virtual                      -1.
% 1.29/1.04  --symbol_type_check                     false
% 1.29/1.04  --clausify_out                          false
% 1.29/1.04  --sig_cnt_out                           false
% 1.29/1.04  --trig_cnt_out                          false
% 1.29/1.04  --trig_cnt_out_tolerance                1.
% 1.29/1.04  --trig_cnt_out_sk_spl                   false
% 1.29/1.04  --abstr_cl_out                          false
% 1.29/1.04  
% 1.29/1.04  ------ Global Options
% 1.29/1.04  
% 1.29/1.04  --schedule                              default
% 1.29/1.04  --add_important_lit                     false
% 1.29/1.04  --prop_solver_per_cl                    1000
% 1.29/1.04  --min_unsat_core                        false
% 1.29/1.04  --soft_assumptions                      false
% 1.29/1.04  --soft_lemma_size                       3
% 1.29/1.04  --prop_impl_unit_size                   0
% 1.29/1.04  --prop_impl_unit                        []
% 1.29/1.04  --share_sel_clauses                     true
% 1.29/1.04  --reset_solvers                         false
% 1.29/1.04  --bc_imp_inh                            [conj_cone]
% 1.29/1.04  --conj_cone_tolerance                   3.
% 1.29/1.04  --extra_neg_conj                        none
% 1.29/1.04  --large_theory_mode                     true
% 1.29/1.04  --prolific_symb_bound                   200
% 1.29/1.04  --lt_threshold                          2000
% 1.29/1.04  --clause_weak_htbl                      true
% 1.29/1.04  --gc_record_bc_elim                     false
% 1.29/1.04  
% 1.29/1.04  ------ Preprocessing Options
% 1.29/1.04  
% 1.29/1.04  --preprocessing_flag                    true
% 1.29/1.04  --time_out_prep_mult                    0.1
% 1.29/1.04  --splitting_mode                        input
% 1.29/1.04  --splitting_grd                         true
% 1.29/1.04  --splitting_cvd                         false
% 1.29/1.04  --splitting_cvd_svl                     false
% 1.29/1.04  --splitting_nvd                         32
% 1.29/1.04  --sub_typing                            true
% 1.29/1.04  --prep_gs_sim                           true
% 1.29/1.04  --prep_unflatten                        true
% 1.29/1.04  --prep_res_sim                          true
% 1.29/1.04  --prep_upred                            true
% 1.29/1.04  --prep_sem_filter                       exhaustive
% 1.29/1.04  --prep_sem_filter_out                   false
% 1.29/1.04  --pred_elim                             true
% 1.29/1.04  --res_sim_input                         true
% 1.29/1.04  --eq_ax_congr_red                       true
% 1.29/1.04  --pure_diseq_elim                       true
% 1.29/1.04  --brand_transform                       false
% 1.29/1.04  --non_eq_to_eq                          false
% 1.29/1.04  --prep_def_merge                        true
% 1.29/1.04  --prep_def_merge_prop_impl              false
% 1.29/1.04  --prep_def_merge_mbd                    true
% 1.29/1.04  --prep_def_merge_tr_red                 false
% 1.29/1.04  --prep_def_merge_tr_cl                  false
% 1.29/1.04  --smt_preprocessing                     true
% 1.29/1.04  --smt_ac_axioms                         fast
% 1.29/1.04  --preprocessed_out                      false
% 1.29/1.04  --preprocessed_stats                    false
% 1.29/1.04  
% 1.29/1.04  ------ Abstraction refinement Options
% 1.29/1.04  
% 1.29/1.04  --abstr_ref                             []
% 1.29/1.04  --abstr_ref_prep                        false
% 1.29/1.04  --abstr_ref_until_sat                   false
% 1.29/1.04  --abstr_ref_sig_restrict                funpre
% 1.29/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.29/1.04  --abstr_ref_under                       []
% 1.29/1.04  
% 1.29/1.04  ------ SAT Options
% 1.29/1.04  
% 1.29/1.04  --sat_mode                              false
% 1.29/1.04  --sat_fm_restart_options                ""
% 1.29/1.04  --sat_gr_def                            false
% 1.29/1.04  --sat_epr_types                         true
% 1.29/1.04  --sat_non_cyclic_types                  false
% 1.29/1.04  --sat_finite_models                     false
% 1.29/1.04  --sat_fm_lemmas                         false
% 1.29/1.04  --sat_fm_prep                           false
% 1.29/1.04  --sat_fm_uc_incr                        true
% 1.29/1.04  --sat_out_model                         small
% 1.29/1.04  --sat_out_clauses                       false
% 1.29/1.04  
% 1.29/1.04  ------ QBF Options
% 1.29/1.04  
% 1.29/1.04  --qbf_mode                              false
% 1.29/1.04  --qbf_elim_univ                         false
% 1.29/1.04  --qbf_dom_inst                          none
% 1.29/1.04  --qbf_dom_pre_inst                      false
% 1.29/1.04  --qbf_sk_in                             false
% 1.29/1.04  --qbf_pred_elim                         true
% 1.29/1.04  --qbf_split                             512
% 1.29/1.04  
% 1.29/1.04  ------ BMC1 Options
% 1.29/1.04  
% 1.29/1.04  --bmc1_incremental                      false
% 1.29/1.04  --bmc1_axioms                           reachable_all
% 1.29/1.04  --bmc1_min_bound                        0
% 1.29/1.04  --bmc1_max_bound                        -1
% 1.29/1.04  --bmc1_max_bound_default                -1
% 1.29/1.04  --bmc1_symbol_reachability              true
% 1.29/1.04  --bmc1_property_lemmas                  false
% 1.29/1.04  --bmc1_k_induction                      false
% 1.29/1.04  --bmc1_non_equiv_states                 false
% 1.29/1.04  --bmc1_deadlock                         false
% 1.29/1.04  --bmc1_ucm                              false
% 1.29/1.04  --bmc1_add_unsat_core                   none
% 1.29/1.04  --bmc1_unsat_core_children              false
% 1.29/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.29/1.04  --bmc1_out_stat                         full
% 1.29/1.04  --bmc1_ground_init                      false
% 1.29/1.04  --bmc1_pre_inst_next_state              false
% 1.29/1.04  --bmc1_pre_inst_state                   false
% 1.29/1.04  --bmc1_pre_inst_reach_state             false
% 1.29/1.04  --bmc1_out_unsat_core                   false
% 1.29/1.04  --bmc1_aig_witness_out                  false
% 1.29/1.04  --bmc1_verbose                          false
% 1.29/1.04  --bmc1_dump_clauses_tptp                false
% 1.29/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.29/1.04  --bmc1_dump_file                        -
% 1.29/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.29/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.29/1.04  --bmc1_ucm_extend_mode                  1
% 1.29/1.04  --bmc1_ucm_init_mode                    2
% 1.29/1.04  --bmc1_ucm_cone_mode                    none
% 1.29/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.29/1.04  --bmc1_ucm_relax_model                  4
% 1.29/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.29/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.29/1.04  --bmc1_ucm_layered_model                none
% 1.29/1.04  --bmc1_ucm_max_lemma_size               10
% 1.29/1.04  
% 1.29/1.04  ------ AIG Options
% 1.29/1.04  
% 1.29/1.04  --aig_mode                              false
% 1.29/1.04  
% 1.29/1.04  ------ Instantiation Options
% 1.29/1.04  
% 1.29/1.04  --instantiation_flag                    true
% 1.29/1.04  --inst_sos_flag                         false
% 1.29/1.04  --inst_sos_phase                        true
% 1.29/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.29/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.29/1.04  --inst_lit_sel_side                     none
% 1.29/1.04  --inst_solver_per_active                1400
% 1.29/1.04  --inst_solver_calls_frac                1.
% 1.29/1.04  --inst_passive_queue_type               priority_queues
% 1.29/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.29/1.04  --inst_passive_queues_freq              [25;2]
% 1.29/1.04  --inst_dismatching                      true
% 1.29/1.04  --inst_eager_unprocessed_to_passive     true
% 1.29/1.04  --inst_prop_sim_given                   true
% 1.29/1.04  --inst_prop_sim_new                     false
% 1.29/1.04  --inst_subs_new                         false
% 1.29/1.04  --inst_eq_res_simp                      false
% 1.29/1.04  --inst_subs_given                       false
% 1.29/1.04  --inst_orphan_elimination               true
% 1.29/1.04  --inst_learning_loop_flag               true
% 1.29/1.04  --inst_learning_start                   3000
% 1.29/1.04  --inst_learning_factor                  2
% 1.29/1.04  --inst_start_prop_sim_after_learn       3
% 1.29/1.04  --inst_sel_renew                        solver
% 1.29/1.04  --inst_lit_activity_flag                true
% 1.29/1.04  --inst_restr_to_given                   false
% 1.29/1.04  --inst_activity_threshold               500
% 1.29/1.04  --inst_out_proof                        true
% 1.29/1.04  
% 1.29/1.04  ------ Resolution Options
% 1.29/1.04  
% 1.29/1.04  --resolution_flag                       false
% 1.29/1.04  --res_lit_sel                           adaptive
% 1.29/1.04  --res_lit_sel_side                      none
% 1.29/1.04  --res_ordering                          kbo
% 1.29/1.04  --res_to_prop_solver                    active
% 1.29/1.04  --res_prop_simpl_new                    false
% 1.29/1.04  --res_prop_simpl_given                  true
% 1.29/1.04  --res_passive_queue_type                priority_queues
% 1.29/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.29/1.04  --res_passive_queues_freq               [15;5]
% 1.29/1.04  --res_forward_subs                      full
% 1.29/1.04  --res_backward_subs                     full
% 1.29/1.04  --res_forward_subs_resolution           true
% 1.29/1.04  --res_backward_subs_resolution          true
% 1.29/1.04  --res_orphan_elimination                true
% 1.29/1.04  --res_time_limit                        2.
% 1.29/1.04  --res_out_proof                         true
% 1.29/1.04  
% 1.29/1.04  ------ Superposition Options
% 1.29/1.04  
% 1.29/1.04  --superposition_flag                    true
% 1.29/1.04  --sup_passive_queue_type                priority_queues
% 1.29/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.29/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.29/1.04  --demod_completeness_check              fast
% 1.29/1.04  --demod_use_ground                      true
% 1.29/1.04  --sup_to_prop_solver                    passive
% 1.29/1.04  --sup_prop_simpl_new                    true
% 1.29/1.04  --sup_prop_simpl_given                  true
% 1.29/1.04  --sup_fun_splitting                     false
% 1.29/1.04  --sup_smt_interval                      50000
% 1.29/1.04  
% 1.29/1.04  ------ Superposition Simplification Setup
% 1.29/1.04  
% 1.29/1.04  --sup_indices_passive                   []
% 1.29/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.29/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.29/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.04  --sup_full_bw                           [BwDemod]
% 1.29/1.04  --sup_immed_triv                        [TrivRules]
% 1.29/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.29/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.04  --sup_immed_bw_main                     []
% 1.29/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.29/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.29/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.29/1.04  
% 1.29/1.04  ------ Combination Options
% 1.29/1.04  
% 1.29/1.04  --comb_res_mult                         3
% 1.29/1.04  --comb_sup_mult                         2
% 1.29/1.04  --comb_inst_mult                        10
% 1.29/1.04  
% 1.29/1.04  ------ Debug Options
% 1.29/1.04  
% 1.29/1.04  --dbg_backtrace                         false
% 1.29/1.04  --dbg_dump_prop_clauses                 false
% 1.29/1.04  --dbg_dump_prop_clauses_file            -
% 1.29/1.04  --dbg_out_stat                          false
% 1.29/1.04  
% 1.29/1.04  
% 1.29/1.04  
% 1.29/1.04  
% 1.29/1.04  ------ Proving...
% 1.29/1.04  
% 1.29/1.04  
% 1.29/1.04  % SZS status Theorem for theBenchmark.p
% 1.29/1.04  
% 1.29/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.29/1.04  
% 1.29/1.04  fof(f16,conjecture,(
% 1.29/1.04    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f17,negated_conjecture,(
% 1.29/1.04    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.29/1.04    inference(negated_conjecture,[],[f16])).
% 1.29/1.04  
% 1.29/1.04  fof(f31,plain,(
% 1.29/1.04    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.29/1.04    inference(ennf_transformation,[],[f17])).
% 1.29/1.04  
% 1.29/1.04  fof(f32,plain,(
% 1.29/1.04    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.29/1.04    inference(flattening,[],[f31])).
% 1.29/1.04  
% 1.29/1.04  fof(f45,plain,(
% 1.29/1.04    ( ! [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) => (r2_hidden(sK4,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.29/1.04    introduced(choice_axiom,[])).
% 1.29/1.04  
% 1.29/1.04  fof(f44,plain,(
% 1.29/1.04    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 1.29/1.04    introduced(choice_axiom,[])).
% 1.29/1.04  
% 1.29/1.04  fof(f46,plain,(
% 1.29/1.04    (r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 1.29/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f45,f44])).
% 1.29/1.04  
% 1.29/1.04  fof(f81,plain,(
% 1.29/1.04    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.29/1.04    inference(cnf_transformation,[],[f46])).
% 1.29/1.04  
% 1.29/1.04  fof(f14,axiom,(
% 1.29/1.04    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f27,plain,(
% 1.29/1.04    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.29/1.04    inference(ennf_transformation,[],[f14])).
% 1.29/1.04  
% 1.29/1.04  fof(f28,plain,(
% 1.29/1.04    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.29/1.04    inference(flattening,[],[f27])).
% 1.29/1.04  
% 1.29/1.04  fof(f74,plain,(
% 1.29/1.04    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f28])).
% 1.29/1.04  
% 1.29/1.04  fof(f1,axiom,(
% 1.29/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f47,plain,(
% 1.29/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f1])).
% 1.29/1.04  
% 1.29/1.04  fof(f2,axiom,(
% 1.29/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f48,plain,(
% 1.29/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f2])).
% 1.29/1.04  
% 1.29/1.04  fof(f3,axiom,(
% 1.29/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f49,plain,(
% 1.29/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f3])).
% 1.29/1.04  
% 1.29/1.04  fof(f4,axiom,(
% 1.29/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f50,plain,(
% 1.29/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f4])).
% 1.29/1.04  
% 1.29/1.04  fof(f5,axiom,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f51,plain,(
% 1.29/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f5])).
% 1.29/1.04  
% 1.29/1.04  fof(f6,axiom,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f52,plain,(
% 1.29/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f6])).
% 1.29/1.04  
% 1.29/1.04  fof(f7,axiom,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f53,plain,(
% 1.29/1.04    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f7])).
% 1.29/1.04  
% 1.29/1.04  fof(f83,plain,(
% 1.29/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.29/1.04    inference(definition_unfolding,[],[f52,f53])).
% 1.29/1.04  
% 1.29/1.04  fof(f84,plain,(
% 1.29/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.29/1.04    inference(definition_unfolding,[],[f51,f83])).
% 1.29/1.04  
% 1.29/1.04  fof(f85,plain,(
% 1.29/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.29/1.04    inference(definition_unfolding,[],[f50,f84])).
% 1.29/1.04  
% 1.29/1.04  fof(f86,plain,(
% 1.29/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.29/1.04    inference(definition_unfolding,[],[f49,f85])).
% 1.29/1.04  
% 1.29/1.04  fof(f87,plain,(
% 1.29/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.29/1.04    inference(definition_unfolding,[],[f48,f86])).
% 1.29/1.04  
% 1.29/1.04  fof(f88,plain,(
% 1.29/1.04    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.29/1.04    inference(definition_unfolding,[],[f47,f87])).
% 1.29/1.04  
% 1.29/1.04  fof(f90,plain,(
% 1.29/1.04    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.29/1.04    inference(definition_unfolding,[],[f74,f88])).
% 1.29/1.04  
% 1.29/1.04  fof(f13,axiom,(
% 1.29/1.04    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f26,plain,(
% 1.29/1.04    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.29/1.04    inference(ennf_transformation,[],[f13])).
% 1.29/1.04  
% 1.29/1.04  fof(f73,plain,(
% 1.29/1.04    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f26])).
% 1.29/1.04  
% 1.29/1.04  fof(f12,axiom,(
% 1.29/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f24,plain,(
% 1.29/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.29/1.04    inference(ennf_transformation,[],[f12])).
% 1.29/1.04  
% 1.29/1.04  fof(f25,plain,(
% 1.29/1.04    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.29/1.04    inference(flattening,[],[f24])).
% 1.29/1.04  
% 1.29/1.04  fof(f72,plain,(
% 1.29/1.04    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f25])).
% 1.29/1.04  
% 1.29/1.04  fof(f76,plain,(
% 1.29/1.04    ~v2_struct_0(sK3)),
% 1.29/1.04    inference(cnf_transformation,[],[f46])).
% 1.29/1.04  
% 1.29/1.04  fof(f80,plain,(
% 1.29/1.04    l1_orders_2(sK3)),
% 1.29/1.04    inference(cnf_transformation,[],[f46])).
% 1.29/1.04  
% 1.29/1.04  fof(f8,axiom,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f18,plain,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.29/1.04    inference(ennf_transformation,[],[f8])).
% 1.29/1.04  
% 1.29/1.04  fof(f34,plain,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.29/1.04    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.29/1.04  
% 1.29/1.04  fof(f33,plain,(
% 1.29/1.04    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 1.29/1.04    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.29/1.04  
% 1.29/1.04  fof(f35,plain,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.29/1.04    inference(definition_folding,[],[f18,f34,f33])).
% 1.29/1.04  
% 1.29/1.04  fof(f43,plain,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.29/1.04    inference(nnf_transformation,[],[f35])).
% 1.29/1.04  
% 1.29/1.04  fof(f67,plain,(
% 1.29/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.29/1.04    inference(cnf_transformation,[],[f43])).
% 1.29/1.04  
% 1.29/1.04  fof(f99,plain,(
% 1.29/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.29/1.04    inference(equality_resolution,[],[f67])).
% 1.29/1.04  
% 1.29/1.04  fof(f40,plain,(
% 1.29/1.04    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.29/1.04    inference(nnf_transformation,[],[f33])).
% 1.29/1.04  
% 1.29/1.04  fof(f41,plain,(
% 1.29/1.04    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.29/1.04    inference(flattening,[],[f40])).
% 1.29/1.04  
% 1.29/1.04  fof(f42,plain,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.29/1.04    inference(rectify,[],[f41])).
% 1.29/1.04  
% 1.29/1.04  fof(f66,plain,(
% 1.29/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 1.29/1.04    inference(cnf_transformation,[],[f42])).
% 1.29/1.04  
% 1.29/1.04  fof(f91,plain,(
% 1.29/1.04    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.29/1.04    inference(equality_resolution,[],[f66])).
% 1.29/1.04  
% 1.29/1.04  fof(f36,plain,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.29/1.04    inference(nnf_transformation,[],[f34])).
% 1.29/1.04  
% 1.29/1.04  fof(f37,plain,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.29/1.04    inference(rectify,[],[f36])).
% 1.29/1.04  
% 1.29/1.04  fof(f38,plain,(
% 1.29/1.04    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.29/1.04    introduced(choice_axiom,[])).
% 1.29/1.04  
% 1.29/1.04  fof(f39,plain,(
% 1.29/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.29/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 1.29/1.04  
% 1.29/1.04  fof(f55,plain,(
% 1.29/1.04    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f39])).
% 1.29/1.04  
% 1.29/1.04  fof(f82,plain,(
% 1.29/1.04    r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))),
% 1.29/1.04    inference(cnf_transformation,[],[f46])).
% 1.29/1.04  
% 1.29/1.04  fof(f9,axiom,(
% 1.29/1.04    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f19,plain,(
% 1.29/1.04    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.29/1.04    inference(ennf_transformation,[],[f9])).
% 1.29/1.04  
% 1.29/1.04  fof(f69,plain,(
% 1.29/1.04    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f19])).
% 1.29/1.04  
% 1.29/1.04  fof(f89,plain,(
% 1.29/1.04    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.29/1.04    inference(definition_unfolding,[],[f69,f88])).
% 1.29/1.04  
% 1.29/1.04  fof(f15,axiom,(
% 1.29/1.04    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f29,plain,(
% 1.29/1.04    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.29/1.04    inference(ennf_transformation,[],[f15])).
% 1.29/1.04  
% 1.29/1.04  fof(f30,plain,(
% 1.29/1.04    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.29/1.04    inference(flattening,[],[f29])).
% 1.29/1.04  
% 1.29/1.04  fof(f75,plain,(
% 1.29/1.04    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f30])).
% 1.29/1.04  
% 1.29/1.04  fof(f79,plain,(
% 1.29/1.04    v5_orders_2(sK3)),
% 1.29/1.04    inference(cnf_transformation,[],[f46])).
% 1.29/1.04  
% 1.29/1.04  fof(f77,plain,(
% 1.29/1.04    v3_orders_2(sK3)),
% 1.29/1.04    inference(cnf_transformation,[],[f46])).
% 1.29/1.04  
% 1.29/1.04  fof(f78,plain,(
% 1.29/1.04    v4_orders_2(sK3)),
% 1.29/1.04    inference(cnf_transformation,[],[f46])).
% 1.29/1.04  
% 1.29/1.04  fof(f11,axiom,(
% 1.29/1.04    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f22,plain,(
% 1.29/1.04    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.29/1.04    inference(ennf_transformation,[],[f11])).
% 1.29/1.04  
% 1.29/1.04  fof(f23,plain,(
% 1.29/1.04    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.29/1.04    inference(flattening,[],[f22])).
% 1.29/1.04  
% 1.29/1.04  fof(f71,plain,(
% 1.29/1.04    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f23])).
% 1.29/1.04  
% 1.29/1.04  fof(f10,axiom,(
% 1.29/1.04    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.29/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.29/1.04  
% 1.29/1.04  fof(f20,plain,(
% 1.29/1.04    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.29/1.04    inference(ennf_transformation,[],[f10])).
% 1.29/1.04  
% 1.29/1.04  fof(f21,plain,(
% 1.29/1.04    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.29/1.04    inference(flattening,[],[f20])).
% 1.29/1.04  
% 1.29/1.04  fof(f70,plain,(
% 1.29/1.04    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.29/1.04    inference(cnf_transformation,[],[f21])).
% 1.29/1.04  
% 1.29/1.04  cnf(c_23,negated_conjecture,
% 1.29/1.04      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 1.29/1.04      inference(cnf_transformation,[],[f81]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2047,plain,
% 1.29/1.04      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_20,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,X1)
% 1.29/1.04      | v1_xboole_0(X1)
% 1.29/1.04      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 1.29/1.04      inference(cnf_transformation,[],[f90]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_19,plain,
% 1.29/1.04      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 1.29/1.04      inference(cnf_transformation,[],[f73]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_18,plain,
% 1.29/1.04      ( v2_struct_0(X0)
% 1.29/1.04      | ~ l1_struct_0(X0)
% 1.29/1.04      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.29/1.04      inference(cnf_transformation,[],[f72]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_309,plain,
% 1.29/1.04      ( ~ l1_orders_2(X0)
% 1.29/1.04      | v2_struct_0(X0)
% 1.29/1.04      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.29/1.04      inference(resolution,[status(thm)],[c_19,c_18]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_28,negated_conjecture,
% 1.29/1.04      ( ~ v2_struct_0(sK3) ),
% 1.29/1.04      inference(cnf_transformation,[],[f76]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_401,plain,
% 1.29/1.04      ( ~ l1_orders_2(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 1.29/1.04      inference(resolution_lifted,[status(thm)],[c_309,c_28]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_402,plain,
% 1.29/1.04      ( ~ l1_orders_2(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.29/1.04      inference(unflattening,[status(thm)],[c_401]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_24,negated_conjecture,
% 1.29/1.04      ( l1_orders_2(sK3) ),
% 1.29/1.04      inference(cnf_transformation,[],[f80]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_43,plain,
% 1.29/1.04      ( ~ l1_orders_2(sK3) | l1_struct_0(sK3) ),
% 1.29/1.04      inference(instantiation,[status(thm)],[c_19]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_46,plain,
% 1.29/1.04      ( v2_struct_0(sK3)
% 1.29/1.04      | ~ l1_struct_0(sK3)
% 1.29/1.04      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.29/1.04      inference(instantiation,[status(thm)],[c_18]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_404,plain,
% 1.29/1.04      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.29/1.04      inference(global_propositional_subsumption,
% 1.29/1.04                [status(thm)],
% 1.29/1.04                [c_402,c_28,c_24,c_43,c_46]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_414,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,X1)
% 1.29/1.04      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
% 1.29/1.04      | u1_struct_0(sK3) != X1 ),
% 1.29/1.04      inference(resolution_lifted,[status(thm)],[c_20,c_404]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_415,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.29/1.04      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK3),X0) ),
% 1.29/1.04      inference(unflattening,[status(thm)],[c_414]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2045,plain,
% 1.29/1.04      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(u1_struct_0(sK3),X0)
% 1.29/1.04      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2251,plain,
% 1.29/1.04      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(u1_struct_0(sK3),sK4) ),
% 1.29/1.04      inference(superposition,[status(thm)],[c_2047,c_2045]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_14,plain,
% 1.29/1.04      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 1.29/1.04      inference(cnf_transformation,[],[f99]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2051,plain,
% 1.29/1.04      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2730,plain,
% 1.29/1.04      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
% 1.29/1.04      inference(superposition,[status(thm)],[c_2251,c_2051]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_4,plain,
% 1.29/1.04      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 1.29/1.04      inference(cnf_transformation,[],[f91]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2061,plain,
% 1.29/1.04      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2,plain,
% 1.29/1.04      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 1.29/1.04      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 1.29/1.04      | r2_hidden(X0,X9) ),
% 1.29/1.04      inference(cnf_transformation,[],[f55]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2063,plain,
% 1.29/1.04      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 1.29/1.04      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 1.29/1.04      | r2_hidden(X0,X9) = iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_3161,plain,
% 1.29/1.04      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 1.29/1.04      | r2_hidden(X7,X8) = iProver_top ),
% 1.29/1.04      inference(superposition,[status(thm)],[c_2061,c_2063]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_4951,plain,
% 1.29/1.04      ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
% 1.29/1.04      inference(superposition,[status(thm)],[c_2730,c_3161]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_22,negated_conjecture,
% 1.29/1.04      ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 1.29/1.04      inference(cnf_transformation,[],[f82]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2048,plain,
% 1.29/1.04      ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_15,plain,
% 1.29/1.04      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 1.29/1.04      | ~ r2_hidden(X0,X1) ),
% 1.29/1.04      inference(cnf_transformation,[],[f89]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2050,plain,
% 1.29/1.04      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 1.29/1.04      | r2_hidden(X0,X1) != iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2850,plain,
% 1.29/1.04      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(X0)) = iProver_top
% 1.29/1.04      | r2_hidden(sK4,X0) != iProver_top ),
% 1.29/1.04      inference(superposition,[status(thm)],[c_2251,c_2050]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_21,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.29/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.29/1.04      | ~ r2_hidden(X0,X2)
% 1.29/1.04      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 1.29/1.04      | ~ v3_orders_2(X1)
% 1.29/1.04      | ~ v4_orders_2(X1)
% 1.29/1.04      | ~ v5_orders_2(X1)
% 1.29/1.04      | ~ l1_orders_2(X1)
% 1.29/1.04      | v2_struct_0(X1) ),
% 1.29/1.04      inference(cnf_transformation,[],[f75]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_25,negated_conjecture,
% 1.29/1.04      ( v5_orders_2(sK3) ),
% 1.29/1.04      inference(cnf_transformation,[],[f79]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_371,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.29/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.29/1.04      | ~ r2_hidden(X0,X2)
% 1.29/1.04      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 1.29/1.04      | ~ v3_orders_2(X1)
% 1.29/1.04      | ~ v4_orders_2(X1)
% 1.29/1.04      | ~ l1_orders_2(X1)
% 1.29/1.04      | v2_struct_0(X1)
% 1.29/1.04      | sK3 != X1 ),
% 1.29/1.04      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_372,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.29/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.29/1.04      | ~ r2_hidden(X0,X1)
% 1.29/1.04      | ~ r2_hidden(X0,k1_orders_2(sK3,X1))
% 1.29/1.04      | ~ v3_orders_2(sK3)
% 1.29/1.04      | ~ v4_orders_2(sK3)
% 1.29/1.04      | ~ l1_orders_2(sK3)
% 1.29/1.04      | v2_struct_0(sK3) ),
% 1.29/1.04      inference(unflattening,[status(thm)],[c_371]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_27,negated_conjecture,
% 1.29/1.04      ( v3_orders_2(sK3) ),
% 1.29/1.04      inference(cnf_transformation,[],[f77]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_26,negated_conjecture,
% 1.29/1.04      ( v4_orders_2(sK3) ),
% 1.29/1.04      inference(cnf_transformation,[],[f78]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_376,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.29/1.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.29/1.04      | ~ r2_hidden(X0,X1)
% 1.29/1.04      | ~ r2_hidden(X0,k1_orders_2(sK3,X1)) ),
% 1.29/1.04      inference(global_propositional_subsumption,
% 1.29/1.04                [status(thm)],
% 1.29/1.04                [c_372,c_28,c_27,c_26,c_24]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_17,plain,
% 1.29/1.04      ( m1_subset_1(X0,X1)
% 1.29/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.29/1.04      | ~ r2_hidden(X0,X2) ),
% 1.29/1.04      inference(cnf_transformation,[],[f71]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_390,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.29/1.04      | ~ r2_hidden(X1,X0)
% 1.29/1.04      | ~ r2_hidden(X1,k1_orders_2(sK3,X0)) ),
% 1.29/1.04      inference(forward_subsumption_resolution,
% 1.29/1.04                [status(thm)],
% 1.29/1.04                [c_376,c_17]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2046,plain,
% 1.29/1.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.29/1.04      | r2_hidden(X1,X0) != iProver_top
% 1.29/1.04      | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2882,plain,
% 1.29/1.04      ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
% 1.29/1.04      | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
% 1.29/1.04      | r2_hidden(sK4,u1_struct_0(sK3)) != iProver_top ),
% 1.29/1.04      inference(superposition,[status(thm)],[c_2850,c_2046]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_34,plain,
% 1.29/1.04      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_16,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.29/1.04      inference(cnf_transformation,[],[f70]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_426,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,X1)
% 1.29/1.04      | r2_hidden(X0,X1)
% 1.29/1.04      | u1_struct_0(sK3) != X1 ),
% 1.29/1.04      inference(resolution_lifted,[status(thm)],[c_16,c_404]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_427,plain,
% 1.29/1.04      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 1.29/1.04      | r2_hidden(X0,u1_struct_0(sK3)) ),
% 1.29/1.04      inference(unflattening,[status(thm)],[c_426]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2206,plain,
% 1.29/1.04      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 1.29/1.04      | r2_hidden(sK4,u1_struct_0(sK3)) ),
% 1.29/1.04      inference(instantiation,[status(thm)],[c_427]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_2207,plain,
% 1.29/1.04      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 1.29/1.04      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
% 1.29/1.04      inference(predicate_to_equality,[status(thm)],[c_2206]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_3931,plain,
% 1.29/1.04      ( r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
% 1.29/1.04      | r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
% 1.29/1.04      inference(global_propositional_subsumption,
% 1.29/1.04                [status(thm)],
% 1.29/1.04                [c_2882,c_34,c_2207]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_3932,plain,
% 1.29/1.04      ( r2_hidden(X0,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top
% 1.29/1.04      | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
% 1.29/1.04      inference(renaming,[status(thm)],[c_3931]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(c_3940,plain,
% 1.29/1.04      ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top ),
% 1.29/1.04      inference(superposition,[status(thm)],[c_2048,c_3932]) ).
% 1.29/1.04  
% 1.29/1.04  cnf(contradiction,plain,
% 1.29/1.04      ( $false ),
% 1.29/1.04      inference(minisat,[status(thm)],[c_4951,c_3940]) ).
% 1.29/1.04  
% 1.29/1.04  
% 1.29/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.29/1.04  
% 1.29/1.04  ------                               Statistics
% 1.29/1.04  
% 1.29/1.04  ------ General
% 1.29/1.04  
% 1.29/1.04  abstr_ref_over_cycles:                  0
% 1.29/1.04  abstr_ref_under_cycles:                 0
% 1.29/1.04  gc_basic_clause_elim:                   0
% 1.29/1.04  forced_gc_time:                         0
% 1.29/1.04  parsing_time:                           0.014
% 1.29/1.04  unif_index_cands_time:                  0.
% 1.29/1.04  unif_index_add_time:                    0.
% 1.29/1.04  orderings_time:                         0.
% 1.29/1.04  out_proof_time:                         0.008
% 1.29/1.04  total_time:                             0.196
% 1.29/1.04  num_of_symbols:                         50
% 1.29/1.04  num_of_terms:                           5648
% 1.29/1.04  
% 1.29/1.04  ------ Preprocessing
% 1.29/1.04  
% 1.29/1.04  num_of_splits:                          0
% 1.29/1.04  num_of_split_atoms:                     0
% 1.29/1.04  num_of_reused_defs:                     0
% 1.29/1.04  num_eq_ax_congr_red:                    100
% 1.29/1.04  num_of_sem_filtered_clauses:            1
% 1.29/1.04  num_of_subtypes:                        0
% 1.29/1.04  monotx_restored_types:                  0
% 1.29/1.04  sat_num_of_epr_types:                   0
% 1.29/1.04  sat_num_of_non_cyclic_types:            0
% 1.29/1.04  sat_guarded_non_collapsed_types:        0
% 1.29/1.04  num_pure_diseq_elim:                    0
% 1.29/1.04  simp_replaced_by:                       0
% 1.29/1.04  res_preprocessed:                       116
% 1.29/1.04  prep_upred:                             0
% 1.29/1.04  prep_unflattend:                        602
% 1.29/1.04  smt_new_axioms:                         0
% 1.29/1.04  pred_elim_cands:                        4
% 1.29/1.04  pred_elim:                              7
% 1.29/1.04  pred_elim_cl:                           7
% 1.29/1.04  pred_elim_cycles:                       12
% 1.29/1.04  merged_defs:                            0
% 1.29/1.04  merged_defs_ncl:                        0
% 1.29/1.04  bin_hyper_res:                          0
% 1.29/1.04  prep_cycles:                            4
% 1.29/1.04  pred_elim_time:                         0.025
% 1.29/1.04  splitting_time:                         0.
% 1.29/1.04  sem_filter_time:                        0.
% 1.29/1.04  monotx_time:                            0.001
% 1.29/1.04  subtype_inf_time:                       0.
% 1.29/1.04  
% 1.29/1.04  ------ Problem properties
% 1.29/1.04  
% 1.29/1.04  clauses:                                22
% 1.29/1.04  conjectures:                            2
% 1.29/1.04  epr:                                    11
% 1.29/1.04  horn:                                   20
% 1.29/1.04  ground:                                 2
% 1.29/1.04  unary:                                  11
% 1.29/1.04  binary:                                 4
% 1.29/1.04  lits:                                   46
% 1.29/1.04  lits_eq:                                10
% 1.29/1.04  fd_pure:                                0
% 1.29/1.04  fd_pseudo:                              0
% 1.29/1.04  fd_cond:                                0
% 1.29/1.04  fd_pseudo_cond:                         2
% 1.29/1.04  ac_symbols:                             0
% 1.29/1.04  
% 1.29/1.04  ------ Propositional Solver
% 1.29/1.04  
% 1.29/1.04  prop_solver_calls:                      28
% 1.29/1.04  prop_fast_solver_calls:                 827
% 1.29/1.04  smt_solver_calls:                       0
% 1.29/1.04  smt_fast_solver_calls:                  0
% 1.29/1.04  prop_num_of_clauses:                    1464
% 1.29/1.04  prop_preprocess_simplified:             6331
% 1.29/1.04  prop_fo_subsumed:                       7
% 1.29/1.04  prop_solver_time:                       0.
% 1.29/1.04  smt_solver_time:                        0.
% 1.29/1.04  smt_fast_solver_time:                   0.
% 1.29/1.04  prop_fast_solver_time:                  0.
% 1.29/1.04  prop_unsat_core_time:                   0.
% 1.29/1.04  
% 1.29/1.04  ------ QBF
% 1.29/1.04  
% 1.29/1.04  qbf_q_res:                              0
% 1.29/1.04  qbf_num_tautologies:                    0
% 1.29/1.04  qbf_prep_cycles:                        0
% 1.29/1.04  
% 1.29/1.04  ------ BMC1
% 1.29/1.04  
% 1.29/1.04  bmc1_current_bound:                     -1
% 1.29/1.04  bmc1_last_solved_bound:                 -1
% 1.29/1.04  bmc1_unsat_core_size:                   -1
% 1.29/1.04  bmc1_unsat_core_parents_size:           -1
% 1.29/1.04  bmc1_merge_next_fun:                    0
% 1.29/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.29/1.04  
% 1.29/1.04  ------ Instantiation
% 1.29/1.04  
% 1.29/1.04  inst_num_of_clauses:                    442
% 1.29/1.04  inst_num_in_passive:                    127
% 1.29/1.04  inst_num_in_active:                     150
% 1.29/1.04  inst_num_in_unprocessed:                165
% 1.29/1.04  inst_num_of_loops:                      180
% 1.29/1.04  inst_num_of_learning_restarts:          0
% 1.29/1.04  inst_num_moves_active_passive:          27
% 1.29/1.04  inst_lit_activity:                      0
% 1.29/1.04  inst_lit_activity_moves:                0
% 1.29/1.04  inst_num_tautologies:                   0
% 1.29/1.04  inst_num_prop_implied:                  0
% 1.29/1.04  inst_num_existing_simplified:           0
% 1.29/1.04  inst_num_eq_res_simplified:             0
% 1.29/1.04  inst_num_child_elim:                    0
% 1.29/1.04  inst_num_of_dismatching_blockings:      142
% 1.29/1.04  inst_num_of_non_proper_insts:           442
% 1.29/1.04  inst_num_of_duplicates:                 0
% 1.29/1.04  inst_inst_num_from_inst_to_res:         0
% 1.29/1.04  inst_dismatching_checking_time:         0.
% 1.29/1.04  
% 1.29/1.04  ------ Resolution
% 1.29/1.04  
% 1.29/1.04  res_num_of_clauses:                     0
% 1.29/1.04  res_num_in_passive:                     0
% 1.29/1.04  res_num_in_active:                      0
% 1.29/1.04  res_num_of_loops:                       120
% 1.29/1.04  res_forward_subset_subsumed:            138
% 1.29/1.04  res_backward_subset_subsumed:           0
% 1.29/1.04  res_forward_subsumed:                   0
% 1.29/1.04  res_backward_subsumed:                  0
% 1.29/1.04  res_forward_subsumption_resolution:     1
% 1.29/1.04  res_backward_subsumption_resolution:    0
% 1.29/1.04  res_clause_to_clause_subsumption:       1009
% 1.29/1.04  res_orphan_elimination:                 0
% 1.29/1.04  res_tautology_del:                      37
% 1.29/1.04  res_num_eq_res_simplified:              0
% 1.29/1.04  res_num_sel_changes:                    0
% 1.29/1.04  res_moves_from_active_to_pass:          0
% 1.29/1.04  
% 1.29/1.04  ------ Superposition
% 1.29/1.04  
% 1.29/1.04  sup_time_total:                         0.
% 1.29/1.04  sup_time_generating:                    0.
% 1.29/1.04  sup_time_sim_full:                      0.
% 1.29/1.04  sup_time_sim_immed:                     0.
% 1.29/1.04  
% 1.29/1.04  sup_num_of_clauses:                     61
% 1.29/1.04  sup_num_in_active:                      36
% 1.29/1.04  sup_num_in_passive:                     25
% 1.29/1.04  sup_num_of_loops:                       35
% 1.29/1.04  sup_fw_superposition:                   37
% 1.29/1.04  sup_bw_superposition:                   17
% 1.29/1.04  sup_immediate_simplified:               3
% 1.29/1.04  sup_given_eliminated:                   0
% 1.29/1.04  comparisons_done:                       0
% 1.29/1.04  comparisons_avoided:                    0
% 1.29/1.04  
% 1.29/1.04  ------ Simplifications
% 1.29/1.04  
% 1.29/1.04  
% 1.29/1.04  sim_fw_subset_subsumed:                 0
% 1.29/1.04  sim_bw_subset_subsumed:                 0
% 1.29/1.04  sim_fw_subsumed:                        1
% 1.29/1.04  sim_bw_subsumed:                        0
% 1.29/1.04  sim_fw_subsumption_res:                 0
% 1.29/1.04  sim_bw_subsumption_res:                 0
% 1.29/1.04  sim_tautology_del:                      3
% 1.29/1.04  sim_eq_tautology_del:                   3
% 1.29/1.04  sim_eq_res_simp:                        0
% 1.29/1.04  sim_fw_demodulated:                     0
% 1.29/1.04  sim_bw_demodulated:                     0
% 1.29/1.04  sim_light_normalised:                   2
% 1.29/1.04  sim_joinable_taut:                      0
% 1.29/1.04  sim_joinable_simp:                      0
% 1.29/1.04  sim_ac_normalised:                      0
% 1.29/1.04  sim_smt_subsumption:                    0
% 1.29/1.04  
%------------------------------------------------------------------------------
