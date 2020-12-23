%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:21 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 303 expanded)
%              Number of clauses        :   50 (  69 expanded)
%              Number of leaves         :   19 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :  471 (1614 expanded)
%              Number of equality atoms :  149 ( 159 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( r2_hidden(sK4,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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

fof(f42,plain,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f41,f40])).

fof(f75,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f80])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f81])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f76,plain,(
    r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
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

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f17,f30,f29])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f63])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f62])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f26])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1995,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1997,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2409,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(u1_struct_0(sK3),sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1995,c_1997])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1996,plain,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_26,c_25])).

cnf(c_1992,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_26,c_25,c_24,c_22])).

cnf(c_1993,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1998,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3186,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1993,c_1998])).

cnf(c_3570,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X0))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1992,c_3186])).

cnf(c_3694,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1996,c_3570])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3793,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3694,c_32])).

cnf(c_3798,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(u1_struct_0(sK3),sK4) ),
    inference(superposition,[status(thm)],[c_2409,c_3793])).

cnf(c_14,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1999,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4012,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3798,c_1999])).

cnf(c_4,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2009,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2011,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4159,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2009,c_2011])).

cnf(c_5197,plain,
    ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4012,c_4159])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k1_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k1_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK3,X1))
    | v2_struct_0(sK3)
    | ~ v3_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ l1_orders_2(sK3) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_orders_2(sK3,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_26,c_25,c_24,c_22])).

cnf(c_2161,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,X0)
    | ~ r2_hidden(sK4,k1_orders_2(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_2234,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4))
    | ~ r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_2235,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
    | r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2234])).

cnf(c_2158,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_2159,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2158])).

cnf(c_33,plain,
    ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5197,c_2235,c_2159,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.78/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.00  
% 2.78/1.00  ------  iProver source info
% 2.78/1.00  
% 2.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.00  git: non_committed_changes: false
% 2.78/1.00  git: last_make_outside_of_git: false
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     num_symb
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       true
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  ------ Parsing...
% 2.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.00  ------ Proving...
% 2.78/1.00  ------ Problem Properties 
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  clauses                                 22
% 2.78/1.00  conjectures                             2
% 2.78/1.00  EPR                                     11
% 2.78/1.00  Horn                                    19
% 2.78/1.00  unary                                   11
% 2.78/1.00  binary                                  3
% 2.78/1.00  lits                                    48
% 2.78/1.00  lits eq                                 10
% 2.78/1.00  fd_pure                                 0
% 2.78/1.00  fd_pseudo                               0
% 2.78/1.00  fd_cond                                 0
% 2.78/1.00  fd_pseudo_cond                          2
% 2.78/1.00  AC symbols                              0
% 2.78/1.00  
% 2.78/1.00  ------ Schedule dynamic 5 is on 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  Current options:
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     none
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       false
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ Proving...
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS status Theorem for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  fof(f14,conjecture,(
% 2.78/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f15,negated_conjecture,(
% 2.78/1.00    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.78/1.00    inference(negated_conjecture,[],[f14])).
% 2.78/1.00  
% 2.78/1.00  fof(f27,plain,(
% 2.78/1.00    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f15])).
% 2.78/1.00  
% 2.78/1.00  fof(f28,plain,(
% 2.78/1.00    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.78/1.00    inference(flattening,[],[f27])).
% 2.78/1.00  
% 2.78/1.00  fof(f41,plain,(
% 2.78/1.00    ( ! [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) => (r2_hidden(sK4,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK4))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f40,plain,(
% 2.78/1.00    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X1))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f42,plain,(
% 2.78/1.00    (r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f41,f40])).
% 2.78/1.00  
% 2.78/1.00  fof(f75,plain,(
% 2.78/1.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.78/1.00    inference(cnf_transformation,[],[f42])).
% 2.78/1.00  
% 2.78/1.00  fof(f11,axiom,(
% 2.78/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f21,plain,(
% 2.78/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f11])).
% 2.78/1.00  
% 2.78/1.00  fof(f22,plain,(
% 2.78/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.78/1.00    inference(flattening,[],[f21])).
% 2.78/1.00  
% 2.78/1.00  fof(f67,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f22])).
% 2.78/1.00  
% 2.78/1.00  fof(f1,axiom,(
% 2.78/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f43,plain,(
% 2.78/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f1])).
% 2.78/1.00  
% 2.78/1.00  fof(f2,axiom,(
% 2.78/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f44,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f2])).
% 2.78/1.00  
% 2.78/1.00  fof(f3,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f45,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f3])).
% 2.78/1.00  
% 2.78/1.00  fof(f4,axiom,(
% 2.78/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f46,plain,(
% 2.78/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f4])).
% 2.78/1.00  
% 2.78/1.00  fof(f5,axiom,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f47,plain,(
% 2.78/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f5])).
% 2.78/1.00  
% 2.78/1.00  fof(f6,axiom,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f48,plain,(
% 2.78/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f6])).
% 2.78/1.00  
% 2.78/1.00  fof(f7,axiom,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f49,plain,(
% 2.78/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f7])).
% 2.78/1.00  
% 2.78/1.00  fof(f77,plain,(
% 2.78/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f48,f49])).
% 2.78/1.00  
% 2.78/1.00  fof(f78,plain,(
% 2.78/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f47,f77])).
% 2.78/1.00  
% 2.78/1.00  fof(f79,plain,(
% 2.78/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f46,f78])).
% 2.78/1.00  
% 2.78/1.00  fof(f80,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f45,f79])).
% 2.78/1.00  
% 2.78/1.00  fof(f81,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f44,f80])).
% 2.78/1.00  
% 2.78/1.00  fof(f82,plain,(
% 2.78/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f43,f81])).
% 2.78/1.00  
% 2.78/1.00  fof(f83,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.78/1.00    inference(definition_unfolding,[],[f67,f82])).
% 2.78/1.00  
% 2.78/1.00  fof(f76,plain,(
% 2.78/1.00    r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))),
% 2.78/1.00    inference(cnf_transformation,[],[f42])).
% 2.78/1.00  
% 2.78/1.00  fof(f12,axiom,(
% 2.78/1.00    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f16,plain,(
% 2.78/1.00    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.78/1.00    inference(pure_predicate_removal,[],[f12])).
% 2.78/1.00  
% 2.78/1.00  fof(f23,plain,(
% 2.78/1.00    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f16])).
% 2.78/1.00  
% 2.78/1.00  fof(f24,plain,(
% 2.78/1.00    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.00    inference(flattening,[],[f23])).
% 2.78/1.00  
% 2.78/1.00  fof(f68,plain,(
% 2.78/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f24])).
% 2.78/1.00  
% 2.78/1.00  fof(f74,plain,(
% 2.78/1.00    l1_orders_2(sK3)),
% 2.78/1.00    inference(cnf_transformation,[],[f42])).
% 2.78/1.00  
% 2.78/1.00  fof(f70,plain,(
% 2.78/1.00    ~v2_struct_0(sK3)),
% 2.78/1.00    inference(cnf_transformation,[],[f42])).
% 2.78/1.00  
% 2.78/1.00  fof(f71,plain,(
% 2.78/1.00    v3_orders_2(sK3)),
% 2.78/1.00    inference(cnf_transformation,[],[f42])).
% 2.78/1.00  
% 2.78/1.00  fof(f10,axiom,(
% 2.78/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f19,plain,(
% 2.78/1.00    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f10])).
% 2.78/1.00  
% 2.78/1.00  fof(f20,plain,(
% 2.78/1.00    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.00    inference(flattening,[],[f19])).
% 2.78/1.00  
% 2.78/1.00  fof(f66,plain,(
% 2.78/1.00    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f20])).
% 2.78/1.00  
% 2.78/1.00  fof(f73,plain,(
% 2.78/1.00    v5_orders_2(sK3)),
% 2.78/1.00    inference(cnf_transformation,[],[f42])).
% 2.78/1.00  
% 2.78/1.00  fof(f72,plain,(
% 2.78/1.00    v4_orders_2(sK3)),
% 2.78/1.00    inference(cnf_transformation,[],[f42])).
% 2.78/1.00  
% 2.78/1.00  fof(f9,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f18,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.78/1.00    inference(ennf_transformation,[],[f9])).
% 2.78/1.00  
% 2.78/1.00  fof(f65,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f18])).
% 2.78/1.00  
% 2.78/1.00  fof(f8,axiom,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f17,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 2.78/1.00    inference(ennf_transformation,[],[f8])).
% 2.78/1.00  
% 2.78/1.00  fof(f30,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.78/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.78/1.00  
% 2.78/1.00  fof(f29,plain,(
% 2.78/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.78/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.78/1.00  
% 2.78/1.00  fof(f31,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 2.78/1.00    inference(definition_folding,[],[f17,f30,f29])).
% 2.78/1.00  
% 2.78/1.00  fof(f39,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 2.78/1.00    inference(nnf_transformation,[],[f31])).
% 2.78/1.00  
% 2.78/1.00  fof(f63,plain,(
% 2.78/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 2.78/1.00    inference(cnf_transformation,[],[f39])).
% 2.78/1.00  
% 2.78/1.00  fof(f92,plain,(
% 2.78/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.78/1.00    inference(equality_resolution,[],[f63])).
% 2.78/1.00  
% 2.78/1.00  fof(f36,plain,(
% 2.78/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.78/1.00    inference(nnf_transformation,[],[f29])).
% 2.78/1.00  
% 2.78/1.00  fof(f37,plain,(
% 2.78/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.78/1.00    inference(flattening,[],[f36])).
% 2.78/1.00  
% 2.78/1.00  fof(f38,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.78/1.00    inference(rectify,[],[f37])).
% 2.78/1.00  
% 2.78/1.00  fof(f62,plain,(
% 2.78/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 2.78/1.00    inference(cnf_transformation,[],[f38])).
% 2.78/1.00  
% 2.78/1.00  fof(f84,plain,(
% 2.78/1.00    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.78/1.00    inference(equality_resolution,[],[f62])).
% 2.78/1.00  
% 2.78/1.00  fof(f32,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.78/1.00    inference(nnf_transformation,[],[f30])).
% 2.78/1.00  
% 2.78/1.00  fof(f33,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.78/1.00    inference(rectify,[],[f32])).
% 2.78/1.00  
% 2.78/1.00  fof(f34,plain,(
% 2.78/1.00    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f35,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f51,plain,(
% 2.78/1.00    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f35])).
% 2.78/1.00  
% 2.78/1.00  fof(f13,axiom,(
% 2.78/1.00    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 2.78/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f25,plain,(
% 2.78/1.00    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f13])).
% 2.78/1.00  
% 2.78/1.00  fof(f26,plain,(
% 2.78/1.00    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.78/1.00    inference(flattening,[],[f25])).
% 2.78/1.00  
% 2.78/1.00  fof(f69,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f26])).
% 2.78/1.00  
% 2.78/1.00  cnf(c_21,negated_conjecture,
% 2.78/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1995,plain,
% 2.78/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_17,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,X1)
% 2.78/1.00      | v1_xboole_0(X1)
% 2.78/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1997,plain,
% 2.78/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
% 2.78/1.00      | m1_subset_1(X0,X1) != iProver_top
% 2.78/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2409,plain,
% 2.78/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(u1_struct_0(sK3),sK4)
% 2.78/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1995,c_1997]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_20,negated_conjecture,
% 2.78/1.00      ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 2.78/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1996,plain,
% 2.78/1.00      ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_18,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/1.00      | v2_struct_0(X1)
% 2.78/1.00      | ~ v3_orders_2(X1)
% 2.78/1.00      | ~ l1_orders_2(X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_22,negated_conjecture,
% 2.78/1.00      ( l1_orders_2(sK3) ),
% 2.78/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_355,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/1.00      | v2_struct_0(X1)
% 2.78/1.00      | ~ v3_orders_2(X1)
% 2.78/1.00      | sK3 != X1 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_356,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.78/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/1.00      | v2_struct_0(sK3)
% 2.78/1.00      | ~ v3_orders_2(sK3) ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_355]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_26,negated_conjecture,
% 2.78/1.00      ( ~ v2_struct_0(sK3) ),
% 2.78/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_25,negated_conjecture,
% 2.78/1.00      ( v3_orders_2(sK3) ),
% 2.78/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_360,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.78/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_356,c_26,c_25]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1992,plain,
% 2.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.78/1.00      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_16,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/1.00      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/1.00      | v2_struct_0(X1)
% 2.78/1.00      | ~ v3_orders_2(X1)
% 2.78/1.00      | ~ v4_orders_2(X1)
% 2.78/1.00      | ~ v5_orders_2(X1)
% 2.78/1.00      | ~ l1_orders_2(X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_23,negated_conjecture,
% 2.78/1.00      ( v5_orders_2(sK3) ),
% 2.78/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_329,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/1.00      | m1_subset_1(k1_orders_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/1.00      | v2_struct_0(X1)
% 2.78/1.00      | ~ v3_orders_2(X1)
% 2.78/1.00      | ~ v4_orders_2(X1)
% 2.78/1.00      | ~ l1_orders_2(X1)
% 2.78/1.00      | sK3 != X1 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_330,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/1.00      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/1.00      | v2_struct_0(sK3)
% 2.78/1.00      | ~ v3_orders_2(sK3)
% 2.78/1.00      | ~ v4_orders_2(sK3)
% 2.78/1.00      | ~ l1_orders_2(sK3) ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_329]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_24,negated_conjecture,
% 2.78/1.00      ( v4_orders_2(sK3) ),
% 2.78/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_334,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/1.00      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_330,c_26,c_25,c_24,c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1993,plain,
% 2.78/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.78/1.00      | m1_subset_1(k1_orders_2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_15,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/1.00      | ~ r2_hidden(X2,X0)
% 2.78/1.00      | ~ v1_xboole_0(X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1998,plain,
% 2.78/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.78/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.78/1.00      | v1_xboole_0(X1) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3186,plain,
% 2.78/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.78/1.00      | r2_hidden(X1,k1_orders_2(sK3,X0)) != iProver_top
% 2.78/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1993,c_1998]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3570,plain,
% 2.78/1.00      ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 2.78/1.00      | r2_hidden(X1,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X0))) != iProver_top
% 2.78/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1992,c_3186]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3694,plain,
% 2.78/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.78/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1996,c_3570]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_32,plain,
% 2.78/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3793,plain,
% 2.78/1.00      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_3694,c_32]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3798,plain,
% 2.78/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(u1_struct_0(sK3),sK4) ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_2409,c_3793]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_14,plain,
% 2.78/1.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1999,plain,
% 2.78/1.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4012,plain,
% 2.78/1.00      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_3798,c_1999]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4,plain,
% 2.78/1.00      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 2.78/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2009,plain,
% 2.78/1.00      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2,plain,
% 2.78/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.78/1.00      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 2.78/1.00      | r2_hidden(X0,X9) ),
% 2.78/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2011,plain,
% 2.78/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.78/1.00      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 2.78/1.00      | r2_hidden(X0,X9) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4159,plain,
% 2.78/1.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.78/1.00      | r2_hidden(X7,X8) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_2009,c_2011]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_5197,plain,
% 2.78/1.00      ( r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_4012,c_4159]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_19,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/1.00      | ~ r2_hidden(X0,X2)
% 2.78/1.00      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 2.78/1.00      | v2_struct_0(X1)
% 2.78/1.00      | ~ v3_orders_2(X1)
% 2.78/1.00      | ~ v4_orders_2(X1)
% 2.78/1.00      | ~ v5_orders_2(X1)
% 2.78/1.00      | ~ l1_orders_2(X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_305,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/1.00      | ~ r2_hidden(X0,X2)
% 2.78/1.00      | ~ r2_hidden(X0,k1_orders_2(X1,X2))
% 2.78/1.00      | v2_struct_0(X1)
% 2.78/1.00      | ~ v3_orders_2(X1)
% 2.78/1.00      | ~ v4_orders_2(X1)
% 2.78/1.00      | ~ l1_orders_2(X1)
% 2.78/1.00      | sK3 != X1 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_306,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/1.00      | ~ r2_hidden(X0,X1)
% 2.78/1.00      | ~ r2_hidden(X0,k1_orders_2(sK3,X1))
% 2.78/1.00      | v2_struct_0(sK3)
% 2.78/1.00      | ~ v3_orders_2(sK3)
% 2.78/1.00      | ~ v4_orders_2(sK3)
% 2.78/1.00      | ~ l1_orders_2(sK3) ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_305]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_310,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.78/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/1.00      | ~ r2_hidden(X0,X1)
% 2.78/1.00      | ~ r2_hidden(X0,k1_orders_2(sK3,X1)) ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_306,c_26,c_25,c_24,c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2161,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.78/1.00      | ~ r2_hidden(sK4,X0)
% 2.78/1.00      | ~ r2_hidden(sK4,k1_orders_2(sK3,X0)) ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_310]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2234,plain,
% 2.78/1.00      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 2.78/1.00      | ~ r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4))
% 2.78/1.00      | ~ r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_2161]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2235,plain,
% 2.78/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.78/1.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 2.78/1.00      | r2_hidden(sK4,k6_domain_1(u1_struct_0(sK3),sK4)) != iProver_top
% 2.78/1.00      | r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_2234]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2158,plain,
% 2.78/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/1.00      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_360]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2159,plain,
% 2.78/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.78/1.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_2158]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_33,plain,
% 2.78/1.00      ( r2_hidden(sK4,k1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(contradiction,plain,
% 2.78/1.00      ( $false ),
% 2.78/1.00      inference(minisat,[status(thm)],[c_5197,c_2235,c_2159,c_33,c_32]) ).
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  ------                               Statistics
% 2.78/1.00  
% 2.78/1.00  ------ General
% 2.78/1.00  
% 2.78/1.00  abstr_ref_over_cycles:                  0
% 2.78/1.00  abstr_ref_under_cycles:                 0
% 2.78/1.00  gc_basic_clause_elim:                   0
% 2.78/1.00  forced_gc_time:                         0
% 2.78/1.00  parsing_time:                           0.009
% 2.78/1.00  unif_index_cands_time:                  0.
% 2.78/1.00  unif_index_add_time:                    0.
% 2.78/1.00  orderings_time:                         0.
% 2.78/1.00  out_proof_time:                         0.008
% 2.78/1.00  total_time:                             0.186
% 2.78/1.00  num_of_symbols:                         49
% 2.78/1.00  num_of_terms:                           4541
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing
% 2.78/1.00  
% 2.78/1.00  num_of_splits:                          0
% 2.78/1.00  num_of_split_atoms:                     0
% 2.78/1.00  num_of_reused_defs:                     0
% 2.78/1.00  num_eq_ax_congr_red:                    102
% 2.78/1.00  num_of_sem_filtered_clauses:            1
% 2.78/1.00  num_of_subtypes:                        0
% 2.78/1.00  monotx_restored_types:                  0
% 2.78/1.00  sat_num_of_epr_types:                   0
% 2.78/1.00  sat_num_of_non_cyclic_types:            0
% 2.78/1.00  sat_guarded_non_collapsed_types:        0
% 2.78/1.00  num_pure_diseq_elim:                    0
% 2.78/1.00  simp_replaced_by:                       0
% 2.78/1.00  res_preprocessed:                       114
% 2.78/1.00  prep_upred:                             0
% 2.78/1.00  prep_unflattend:                        599
% 2.78/1.00  smt_new_axioms:                         0
% 2.78/1.00  pred_elim_cands:                        5
% 2.78/1.00  pred_elim:                              5
% 2.78/1.00  pred_elim_cl:                           5
% 2.78/1.00  pred_elim_cycles:                       11
% 2.78/1.00  merged_defs:                            0
% 2.78/1.00  merged_defs_ncl:                        0
% 2.78/1.00  bin_hyper_res:                          0
% 2.78/1.00  prep_cycles:                            4
% 2.78/1.00  pred_elim_time:                         0.027
% 2.78/1.00  splitting_time:                         0.
% 2.78/1.00  sem_filter_time:                        0.
% 2.78/1.00  monotx_time:                            0.001
% 2.78/1.00  subtype_inf_time:                       0.
% 2.78/1.00  
% 2.78/1.00  ------ Problem properties
% 2.78/1.00  
% 2.78/1.00  clauses:                                22
% 2.78/1.00  conjectures:                            2
% 2.78/1.00  epr:                                    11
% 2.78/1.00  horn:                                   19
% 2.78/1.00  ground:                                 2
% 2.78/1.00  unary:                                  11
% 2.78/1.00  binary:                                 3
% 2.78/1.00  lits:                                   48
% 2.78/1.00  lits_eq:                                10
% 2.78/1.00  fd_pure:                                0
% 2.78/1.00  fd_pseudo:                              0
% 2.78/1.00  fd_cond:                                0
% 2.78/1.00  fd_pseudo_cond:                         2
% 2.78/1.00  ac_symbols:                             0
% 2.78/1.00  
% 2.78/1.00  ------ Propositional Solver
% 2.78/1.00  
% 2.78/1.00  prop_solver_calls:                      27
% 2.78/1.00  prop_fast_solver_calls:                 890
% 2.78/1.00  smt_solver_calls:                       0
% 2.78/1.00  smt_fast_solver_calls:                  0
% 2.78/1.00  prop_num_of_clauses:                    1710
% 2.78/1.00  prop_preprocess_simplified:             5511
% 2.78/1.00  prop_fo_subsumed:                       12
% 2.78/1.00  prop_solver_time:                       0.
% 2.78/1.00  smt_solver_time:                        0.
% 2.78/1.00  smt_fast_solver_time:                   0.
% 2.78/1.00  prop_fast_solver_time:                  0.
% 2.78/1.00  prop_unsat_core_time:                   0.
% 2.78/1.00  
% 2.78/1.00  ------ QBF
% 2.78/1.00  
% 2.78/1.00  qbf_q_res:                              0
% 2.78/1.00  qbf_num_tautologies:                    0
% 2.78/1.00  qbf_prep_cycles:                        0
% 2.78/1.00  
% 2.78/1.00  ------ BMC1
% 2.78/1.00  
% 2.78/1.00  bmc1_current_bound:                     -1
% 2.78/1.00  bmc1_last_solved_bound:                 -1
% 2.78/1.00  bmc1_unsat_core_size:                   -1
% 2.78/1.00  bmc1_unsat_core_parents_size:           -1
% 2.78/1.00  bmc1_merge_next_fun:                    0
% 2.78/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation
% 2.78/1.00  
% 2.78/1.00  inst_num_of_clauses:                    485
% 2.78/1.00  inst_num_in_passive:                    62
% 2.78/1.00  inst_num_in_active:                     216
% 2.78/1.00  inst_num_in_unprocessed:                207
% 2.78/1.00  inst_num_of_loops:                      260
% 2.78/1.00  inst_num_of_learning_restarts:          0
% 2.78/1.00  inst_num_moves_active_passive:          40
% 2.78/1.00  inst_lit_activity:                      0
% 2.78/1.00  inst_lit_activity_moves:                0
% 2.78/1.00  inst_num_tautologies:                   0
% 2.78/1.00  inst_num_prop_implied:                  0
% 2.78/1.00  inst_num_existing_simplified:           0
% 2.78/1.00  inst_num_eq_res_simplified:             0
% 2.78/1.00  inst_num_child_elim:                    0
% 2.78/1.00  inst_num_of_dismatching_blockings:      84
% 2.78/1.00  inst_num_of_non_proper_insts:           434
% 2.78/1.00  inst_num_of_duplicates:                 0
% 2.78/1.00  inst_inst_num_from_inst_to_res:         0
% 2.78/1.00  inst_dismatching_checking_time:         0.
% 2.78/1.00  
% 2.78/1.00  ------ Resolution
% 2.78/1.00  
% 2.78/1.00  res_num_of_clauses:                     0
% 2.78/1.00  res_num_in_passive:                     0
% 2.78/1.00  res_num_in_active:                      0
% 2.78/1.00  res_num_of_loops:                       118
% 2.78/1.00  res_forward_subset_subsumed:            130
% 2.78/1.00  res_backward_subset_subsumed:           0
% 2.78/1.00  res_forward_subsumed:                   0
% 2.78/1.00  res_backward_subsumed:                  0
% 2.78/1.00  res_forward_subsumption_resolution:     0
% 2.78/1.00  res_backward_subsumption_resolution:    0
% 2.78/1.00  res_clause_to_clause_subsumption:       967
% 2.78/1.00  res_orphan_elimination:                 0
% 2.78/1.00  res_tautology_del:                      59
% 2.78/1.00  res_num_eq_res_simplified:              0
% 2.78/1.00  res_num_sel_changes:                    0
% 2.78/1.00  res_moves_from_active_to_pass:          0
% 2.78/1.00  
% 2.78/1.00  ------ Superposition
% 2.78/1.00  
% 2.78/1.00  sup_time_total:                         0.
% 2.78/1.00  sup_time_generating:                    0.
% 2.78/1.00  sup_time_sim_full:                      0.
% 2.78/1.00  sup_time_sim_immed:                     0.
% 2.78/1.00  
% 2.78/1.00  sup_num_of_clauses:                     70
% 2.78/1.00  sup_num_in_active:                      50
% 2.78/1.00  sup_num_in_passive:                     20
% 2.78/1.00  sup_num_of_loops:                       50
% 2.78/1.00  sup_fw_superposition:                   51
% 2.78/1.00  sup_bw_superposition:                   10
% 2.78/1.00  sup_immediate_simplified:               3
% 2.78/1.00  sup_given_eliminated:                   0
% 2.78/1.00  comparisons_done:                       0
% 2.78/1.00  comparisons_avoided:                    0
% 2.78/1.00  
% 2.78/1.00  ------ Simplifications
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  sim_fw_subset_subsumed:                 3
% 2.78/1.00  sim_bw_subset_subsumed:                 1
% 2.78/1.00  sim_fw_subsumed:                        0
% 2.78/1.00  sim_bw_subsumed:                        0
% 2.78/1.00  sim_fw_subsumption_res:                 0
% 2.78/1.00  sim_bw_subsumption_res:                 0
% 2.78/1.00  sim_tautology_del:                      0
% 2.78/1.00  sim_eq_tautology_del:                   3
% 2.78/1.00  sim_eq_res_simp:                        0
% 2.78/1.00  sim_fw_demodulated:                     0
% 2.78/1.00  sim_bw_demodulated:                     0
% 2.78/1.00  sim_light_normalised:                   0
% 2.78/1.00  sim_joinable_taut:                      0
% 2.78/1.00  sim_joinable_simp:                      0
% 2.78/1.00  sim_ac_normalised:                      0
% 2.78/1.00  sim_smt_subsumption:                    0
% 2.78/1.00  
%------------------------------------------------------------------------------
