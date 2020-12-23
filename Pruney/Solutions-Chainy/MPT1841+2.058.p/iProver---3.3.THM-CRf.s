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
% DateTime   : Thu Dec  3 12:25:00 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 434 expanded)
%              Number of clauses        :   62 ( 132 expanded)
%              Number of leaves         :   25 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  462 (1443 expanded)
%              Number of equality atoms :  175 ( 249 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f21,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK7),X0)
        & m1_subset_1(sK7,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK6)
          & v1_subset_1(k6_domain_1(sK6,X1),sK6)
          & m1_subset_1(X1,sK6) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( v1_zfmisc_1(sK6)
    & v1_subset_1(k6_domain_1(sK6,sK7),sK6)
    & m1_subset_1(sK7,sK6)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f37,f62,f61])).

fof(f104,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f105,plain,(
    m1_subset_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f106,plain,(
    v1_subset_1(k6_domain_1(sK6,sK7),sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    v1_zfmisc_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f76,f108])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f75,f109])).

fof(f111,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f74,f110])).

fof(f112,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f73,f111])).

fof(f113,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f112])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f102,f113])).

fof(f11,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f38,plain,(
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

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f24,f39,f38])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f92,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f125,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f92])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f117,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f91])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2700,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_25,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2676,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2674,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4396,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_2674])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_37,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_38,plain,
    ( m1_subset_1(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK6,sK7),sK6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_32,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_26,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_189,plain,
    ( ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_26])).

cnf(c_190,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_33,negated_conjecture,
    ( v1_zfmisc_1(sK6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_386,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_190,c_33])).

cnf(c_387,plain,
    ( ~ v1_subset_1(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK6))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6))
    | v1_xboole_0(X0)
    | k6_domain_1(sK6,sK7) != X0
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_387])).

cnf(c_408,plain,
    ( ~ m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6))
    | v1_xboole_0(k6_domain_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_409,plain,
    ( m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2940,plain,
    ( m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK7,sK6)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2941,plain,
    ( m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK7,sK6) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2940])).

cnf(c_3057,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k6_domain_1(sK6,sK7)))
    | ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(k6_domain_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3272,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k6_domain_1(sK6,sK7)))
    | ~ r2_hidden(X0,k1_xboole_0)
    | ~ v1_xboole_0(k6_domain_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_3057])).

cnf(c_3274,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k6_domain_1(sK6,sK7))) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k6_domain_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3272])).

cnf(c_3273,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k6_domain_1(sK6,sK7))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3278,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k6_domain_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3273])).

cnf(c_8062,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4396,c_37,c_38,c_409,c_2941,c_3274,c_3278])).

cnf(c_8069,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2700,c_8062])).

cnf(c_2668,plain,
    ( m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_2977,plain,
    ( v1_xboole_0(k6_domain_1(sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2668,c_37,c_38,c_409,c_2941])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2697,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2699,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3836,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_2699])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2695,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4147,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_2695])).

cnf(c_4163,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3836,c_4147])).

cnf(c_4238,plain,
    ( k6_domain_1(sK6,sK7) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_4163])).

cnf(c_8224,plain,
    ( k6_domain_1(sK6,sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8069,c_4238])).

cnf(c_2670,plain,
    ( m1_subset_1(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2671,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3128,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(sK6,sK7)
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2670,c_2671])).

cnf(c_2968,plain,
    ( ~ m1_subset_1(sK7,sK6)
    | v1_xboole_0(sK6)
    | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3453,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(sK6,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3128,c_36,c_35,c_2968])).

cnf(c_22,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2679,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4646,plain,
    ( sP1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7,k6_domain_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3453,c_2679])).

cnf(c_8243,plain,
    ( sP1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8224,c_4646])).

cnf(c_12,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2689,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2691,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5606,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2689,c_2691])).

cnf(c_9515,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8243,c_5606])).

cnf(c_9756,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9515,c_8062])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:13:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.76/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/0.97  
% 2.76/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/0.97  
% 2.76/0.97  ------  iProver source info
% 2.76/0.97  
% 2.76/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.76/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/0.97  git: non_committed_changes: false
% 2.76/0.97  git: last_make_outside_of_git: false
% 2.76/0.97  
% 2.76/0.97  ------ 
% 2.76/0.97  
% 2.76/0.97  ------ Input Options
% 2.76/0.97  
% 2.76/0.97  --out_options                           all
% 2.76/0.97  --tptp_safe_out                         true
% 2.76/0.97  --problem_path                          ""
% 2.76/0.97  --include_path                          ""
% 2.76/0.97  --clausifier                            res/vclausify_rel
% 2.76/0.97  --clausifier_options                    --mode clausify
% 2.76/0.97  --stdin                                 false
% 2.76/0.97  --stats_out                             all
% 2.76/0.97  
% 2.76/0.97  ------ General Options
% 2.76/0.97  
% 2.76/0.97  --fof                                   false
% 2.76/0.97  --time_out_real                         305.
% 2.76/0.97  --time_out_virtual                      -1.
% 2.76/0.97  --symbol_type_check                     false
% 2.76/0.97  --clausify_out                          false
% 2.76/0.97  --sig_cnt_out                           false
% 2.76/0.97  --trig_cnt_out                          false
% 2.76/0.97  --trig_cnt_out_tolerance                1.
% 2.76/0.97  --trig_cnt_out_sk_spl                   false
% 2.76/0.97  --abstr_cl_out                          false
% 2.76/0.97  
% 2.76/0.97  ------ Global Options
% 2.76/0.97  
% 2.76/0.97  --schedule                              default
% 2.76/0.97  --add_important_lit                     false
% 2.76/0.97  --prop_solver_per_cl                    1000
% 2.76/0.97  --min_unsat_core                        false
% 2.76/0.97  --soft_assumptions                      false
% 2.76/0.97  --soft_lemma_size                       3
% 2.76/0.97  --prop_impl_unit_size                   0
% 2.76/0.97  --prop_impl_unit                        []
% 2.76/0.97  --share_sel_clauses                     true
% 2.76/0.97  --reset_solvers                         false
% 2.76/0.97  --bc_imp_inh                            [conj_cone]
% 2.76/0.97  --conj_cone_tolerance                   3.
% 2.76/0.97  --extra_neg_conj                        none
% 2.76/0.97  --large_theory_mode                     true
% 2.76/0.97  --prolific_symb_bound                   200
% 2.76/0.97  --lt_threshold                          2000
% 2.76/0.97  --clause_weak_htbl                      true
% 2.76/0.97  --gc_record_bc_elim                     false
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing Options
% 2.76/0.97  
% 2.76/0.97  --preprocessing_flag                    true
% 2.76/0.97  --time_out_prep_mult                    0.1
% 2.76/0.97  --splitting_mode                        input
% 2.76/0.97  --splitting_grd                         true
% 2.76/0.97  --splitting_cvd                         false
% 2.76/0.97  --splitting_cvd_svl                     false
% 2.76/0.97  --splitting_nvd                         32
% 2.76/0.97  --sub_typing                            true
% 2.76/0.97  --prep_gs_sim                           true
% 2.76/0.97  --prep_unflatten                        true
% 2.76/0.97  --prep_res_sim                          true
% 2.76/0.97  --prep_upred                            true
% 2.76/0.97  --prep_sem_filter                       exhaustive
% 2.76/0.97  --prep_sem_filter_out                   false
% 2.76/0.97  --pred_elim                             true
% 2.76/0.97  --res_sim_input                         true
% 2.76/0.97  --eq_ax_congr_red                       true
% 2.76/0.97  --pure_diseq_elim                       true
% 2.76/0.97  --brand_transform                       false
% 2.76/0.97  --non_eq_to_eq                          false
% 2.76/0.97  --prep_def_merge                        true
% 2.76/0.97  --prep_def_merge_prop_impl              false
% 2.76/0.97  --prep_def_merge_mbd                    true
% 2.76/0.97  --prep_def_merge_tr_red                 false
% 2.76/0.97  --prep_def_merge_tr_cl                  false
% 2.76/0.97  --smt_preprocessing                     true
% 2.76/0.97  --smt_ac_axioms                         fast
% 2.76/0.97  --preprocessed_out                      false
% 2.76/0.97  --preprocessed_stats                    false
% 2.76/0.97  
% 2.76/0.97  ------ Abstraction refinement Options
% 2.76/0.97  
% 2.76/0.97  --abstr_ref                             []
% 2.76/0.97  --abstr_ref_prep                        false
% 2.76/0.97  --abstr_ref_until_sat                   false
% 2.76/0.97  --abstr_ref_sig_restrict                funpre
% 2.76/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.97  --abstr_ref_under                       []
% 2.76/0.97  
% 2.76/0.97  ------ SAT Options
% 2.76/0.97  
% 2.76/0.97  --sat_mode                              false
% 2.76/0.97  --sat_fm_restart_options                ""
% 2.76/0.97  --sat_gr_def                            false
% 2.76/0.97  --sat_epr_types                         true
% 2.76/0.97  --sat_non_cyclic_types                  false
% 2.76/0.97  --sat_finite_models                     false
% 2.76/0.97  --sat_fm_lemmas                         false
% 2.76/0.97  --sat_fm_prep                           false
% 2.76/0.97  --sat_fm_uc_incr                        true
% 2.76/0.97  --sat_out_model                         small
% 2.76/0.97  --sat_out_clauses                       false
% 2.76/0.97  
% 2.76/0.97  ------ QBF Options
% 2.76/0.97  
% 2.76/0.97  --qbf_mode                              false
% 2.76/0.97  --qbf_elim_univ                         false
% 2.76/0.97  --qbf_dom_inst                          none
% 2.76/0.97  --qbf_dom_pre_inst                      false
% 2.76/0.97  --qbf_sk_in                             false
% 2.76/0.97  --qbf_pred_elim                         true
% 2.76/0.97  --qbf_split                             512
% 2.76/0.97  
% 2.76/0.97  ------ BMC1 Options
% 2.76/0.97  
% 2.76/0.97  --bmc1_incremental                      false
% 2.76/0.97  --bmc1_axioms                           reachable_all
% 2.76/0.97  --bmc1_min_bound                        0
% 2.76/0.97  --bmc1_max_bound                        -1
% 2.76/0.97  --bmc1_max_bound_default                -1
% 2.76/0.97  --bmc1_symbol_reachability              true
% 2.76/0.97  --bmc1_property_lemmas                  false
% 2.76/0.97  --bmc1_k_induction                      false
% 2.76/0.97  --bmc1_non_equiv_states                 false
% 2.76/0.97  --bmc1_deadlock                         false
% 2.76/0.97  --bmc1_ucm                              false
% 2.76/0.97  --bmc1_add_unsat_core                   none
% 2.76/0.97  --bmc1_unsat_core_children              false
% 2.76/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.97  --bmc1_out_stat                         full
% 2.76/0.97  --bmc1_ground_init                      false
% 2.76/0.97  --bmc1_pre_inst_next_state              false
% 2.76/0.97  --bmc1_pre_inst_state                   false
% 2.76/0.97  --bmc1_pre_inst_reach_state             false
% 2.76/0.97  --bmc1_out_unsat_core                   false
% 2.76/0.97  --bmc1_aig_witness_out                  false
% 2.76/0.97  --bmc1_verbose                          false
% 2.76/0.97  --bmc1_dump_clauses_tptp                false
% 2.76/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.97  --bmc1_dump_file                        -
% 2.76/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.97  --bmc1_ucm_extend_mode                  1
% 2.76/0.97  --bmc1_ucm_init_mode                    2
% 2.76/0.97  --bmc1_ucm_cone_mode                    none
% 2.76/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.97  --bmc1_ucm_relax_model                  4
% 2.76/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.97  --bmc1_ucm_layered_model                none
% 2.76/0.97  --bmc1_ucm_max_lemma_size               10
% 2.76/0.97  
% 2.76/0.97  ------ AIG Options
% 2.76/0.97  
% 2.76/0.97  --aig_mode                              false
% 2.76/0.97  
% 2.76/0.97  ------ Instantiation Options
% 2.76/0.97  
% 2.76/0.97  --instantiation_flag                    true
% 2.76/0.97  --inst_sos_flag                         false
% 2.76/0.97  --inst_sos_phase                        true
% 2.76/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.97  --inst_lit_sel_side                     num_symb
% 2.76/0.97  --inst_solver_per_active                1400
% 2.76/0.97  --inst_solver_calls_frac                1.
% 2.76/0.97  --inst_passive_queue_type               priority_queues
% 2.76/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.97  --inst_passive_queues_freq              [25;2]
% 2.76/0.97  --inst_dismatching                      true
% 2.76/0.97  --inst_eager_unprocessed_to_passive     true
% 2.76/0.97  --inst_prop_sim_given                   true
% 2.76/0.97  --inst_prop_sim_new                     false
% 2.76/0.97  --inst_subs_new                         false
% 2.76/0.97  --inst_eq_res_simp                      false
% 2.76/0.97  --inst_subs_given                       false
% 2.76/0.97  --inst_orphan_elimination               true
% 2.76/0.97  --inst_learning_loop_flag               true
% 2.76/0.97  --inst_learning_start                   3000
% 2.76/0.97  --inst_learning_factor                  2
% 2.76/0.97  --inst_start_prop_sim_after_learn       3
% 2.76/0.97  --inst_sel_renew                        solver
% 2.76/0.97  --inst_lit_activity_flag                true
% 2.76/0.97  --inst_restr_to_given                   false
% 2.76/0.97  --inst_activity_threshold               500
% 2.76/0.97  --inst_out_proof                        true
% 2.76/0.97  
% 2.76/0.97  ------ Resolution Options
% 2.76/0.97  
% 2.76/0.97  --resolution_flag                       true
% 2.76/0.97  --res_lit_sel                           adaptive
% 2.76/0.97  --res_lit_sel_side                      none
% 2.76/0.97  --res_ordering                          kbo
% 2.76/0.97  --res_to_prop_solver                    active
% 2.76/0.97  --res_prop_simpl_new                    false
% 2.76/0.97  --res_prop_simpl_given                  true
% 2.76/0.97  --res_passive_queue_type                priority_queues
% 2.76/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.97  --res_passive_queues_freq               [15;5]
% 2.76/0.97  --res_forward_subs                      full
% 2.76/0.97  --res_backward_subs                     full
% 2.76/0.97  --res_forward_subs_resolution           true
% 2.76/0.97  --res_backward_subs_resolution          true
% 2.76/0.97  --res_orphan_elimination                true
% 2.76/0.97  --res_time_limit                        2.
% 2.76/0.97  --res_out_proof                         true
% 2.76/0.97  
% 2.76/0.97  ------ Superposition Options
% 2.76/0.97  
% 2.76/0.97  --superposition_flag                    true
% 2.76/0.97  --sup_passive_queue_type                priority_queues
% 2.76/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.97  --demod_completeness_check              fast
% 2.76/0.97  --demod_use_ground                      true
% 2.76/0.97  --sup_to_prop_solver                    passive
% 2.76/0.97  --sup_prop_simpl_new                    true
% 2.76/0.97  --sup_prop_simpl_given                  true
% 2.76/0.97  --sup_fun_splitting                     false
% 2.76/0.97  --sup_smt_interval                      50000
% 2.76/0.97  
% 2.76/0.97  ------ Superposition Simplification Setup
% 2.76/0.97  
% 2.76/0.97  --sup_indices_passive                   []
% 2.76/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_full_bw                           [BwDemod]
% 2.76/0.97  --sup_immed_triv                        [TrivRules]
% 2.76/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_immed_bw_main                     []
% 2.76/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.97  
% 2.76/0.97  ------ Combination Options
% 2.76/0.97  
% 2.76/0.97  --comb_res_mult                         3
% 2.76/0.97  --comb_sup_mult                         2
% 2.76/0.97  --comb_inst_mult                        10
% 2.76/0.97  
% 2.76/0.97  ------ Debug Options
% 2.76/0.97  
% 2.76/0.97  --dbg_backtrace                         false
% 2.76/0.97  --dbg_dump_prop_clauses                 false
% 2.76/0.97  --dbg_dump_prop_clauses_file            -
% 2.76/0.97  --dbg_out_stat                          false
% 2.76/0.97  ------ Parsing...
% 2.76/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/0.97  ------ Proving...
% 2.76/0.97  ------ Problem Properties 
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  clauses                                 33
% 2.76/0.97  conjectures                             2
% 2.76/0.97  EPR                                     18
% 2.76/0.97  Horn                                    27
% 2.76/0.97  unary                                   15
% 2.76/0.97  binary                                  7
% 2.76/0.97  lits                                    68
% 2.76/0.97  lits eq                                 11
% 2.76/0.97  fd_pure                                 0
% 2.76/0.97  fd_pseudo                               0
% 2.76/0.97  fd_cond                                 0
% 2.76/0.97  fd_pseudo_cond                          3
% 2.76/0.97  AC symbols                              0
% 2.76/0.97  
% 2.76/0.97  ------ Schedule dynamic 5 is on 
% 2.76/0.97  
% 2.76/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  ------ 
% 2.76/0.97  Current options:
% 2.76/0.97  ------ 
% 2.76/0.97  
% 2.76/0.97  ------ Input Options
% 2.76/0.97  
% 2.76/0.97  --out_options                           all
% 2.76/0.97  --tptp_safe_out                         true
% 2.76/0.97  --problem_path                          ""
% 2.76/0.97  --include_path                          ""
% 2.76/0.97  --clausifier                            res/vclausify_rel
% 2.76/0.97  --clausifier_options                    --mode clausify
% 2.76/0.97  --stdin                                 false
% 2.76/0.97  --stats_out                             all
% 2.76/0.97  
% 2.76/0.97  ------ General Options
% 2.76/0.97  
% 2.76/0.97  --fof                                   false
% 2.76/0.97  --time_out_real                         305.
% 2.76/0.97  --time_out_virtual                      -1.
% 2.76/0.97  --symbol_type_check                     false
% 2.76/0.97  --clausify_out                          false
% 2.76/0.97  --sig_cnt_out                           false
% 2.76/0.97  --trig_cnt_out                          false
% 2.76/0.97  --trig_cnt_out_tolerance                1.
% 2.76/0.97  --trig_cnt_out_sk_spl                   false
% 2.76/0.97  --abstr_cl_out                          false
% 2.76/0.97  
% 2.76/0.97  ------ Global Options
% 2.76/0.97  
% 2.76/0.97  --schedule                              default
% 2.76/0.97  --add_important_lit                     false
% 2.76/0.97  --prop_solver_per_cl                    1000
% 2.76/0.97  --min_unsat_core                        false
% 2.76/0.97  --soft_assumptions                      false
% 2.76/0.97  --soft_lemma_size                       3
% 2.76/0.97  --prop_impl_unit_size                   0
% 2.76/0.97  --prop_impl_unit                        []
% 2.76/0.97  --share_sel_clauses                     true
% 2.76/0.97  --reset_solvers                         false
% 2.76/0.97  --bc_imp_inh                            [conj_cone]
% 2.76/0.97  --conj_cone_tolerance                   3.
% 2.76/0.97  --extra_neg_conj                        none
% 2.76/0.97  --large_theory_mode                     true
% 2.76/0.97  --prolific_symb_bound                   200
% 2.76/0.97  --lt_threshold                          2000
% 2.76/0.97  --clause_weak_htbl                      true
% 2.76/0.97  --gc_record_bc_elim                     false
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing Options
% 2.76/0.97  
% 2.76/0.97  --preprocessing_flag                    true
% 2.76/0.97  --time_out_prep_mult                    0.1
% 2.76/0.97  --splitting_mode                        input
% 2.76/0.97  --splitting_grd                         true
% 2.76/0.97  --splitting_cvd                         false
% 2.76/0.97  --splitting_cvd_svl                     false
% 2.76/0.97  --splitting_nvd                         32
% 2.76/0.97  --sub_typing                            true
% 2.76/0.97  --prep_gs_sim                           true
% 2.76/0.97  --prep_unflatten                        true
% 2.76/0.97  --prep_res_sim                          true
% 2.76/0.97  --prep_upred                            true
% 2.76/0.97  --prep_sem_filter                       exhaustive
% 2.76/0.97  --prep_sem_filter_out                   false
% 2.76/0.97  --pred_elim                             true
% 2.76/0.97  --res_sim_input                         true
% 2.76/0.97  --eq_ax_congr_red                       true
% 2.76/0.97  --pure_diseq_elim                       true
% 2.76/0.97  --brand_transform                       false
% 2.76/0.97  --non_eq_to_eq                          false
% 2.76/0.97  --prep_def_merge                        true
% 2.76/0.97  --prep_def_merge_prop_impl              false
% 2.76/0.97  --prep_def_merge_mbd                    true
% 2.76/0.97  --prep_def_merge_tr_red                 false
% 2.76/0.97  --prep_def_merge_tr_cl                  false
% 2.76/0.97  --smt_preprocessing                     true
% 2.76/0.97  --smt_ac_axioms                         fast
% 2.76/0.97  --preprocessed_out                      false
% 2.76/0.97  --preprocessed_stats                    false
% 2.76/0.97  
% 2.76/0.97  ------ Abstraction refinement Options
% 2.76/0.97  
% 2.76/0.97  --abstr_ref                             []
% 2.76/0.97  --abstr_ref_prep                        false
% 2.76/0.97  --abstr_ref_until_sat                   false
% 2.76/0.97  --abstr_ref_sig_restrict                funpre
% 2.76/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.97  --abstr_ref_under                       []
% 2.76/0.97  
% 2.76/0.97  ------ SAT Options
% 2.76/0.97  
% 2.76/0.97  --sat_mode                              false
% 2.76/0.97  --sat_fm_restart_options                ""
% 2.76/0.97  --sat_gr_def                            false
% 2.76/0.97  --sat_epr_types                         true
% 2.76/0.97  --sat_non_cyclic_types                  false
% 2.76/0.97  --sat_finite_models                     false
% 2.76/0.97  --sat_fm_lemmas                         false
% 2.76/0.97  --sat_fm_prep                           false
% 2.76/0.97  --sat_fm_uc_incr                        true
% 2.76/0.97  --sat_out_model                         small
% 2.76/0.97  --sat_out_clauses                       false
% 2.76/0.97  
% 2.76/0.97  ------ QBF Options
% 2.76/0.97  
% 2.76/0.97  --qbf_mode                              false
% 2.76/0.97  --qbf_elim_univ                         false
% 2.76/0.97  --qbf_dom_inst                          none
% 2.76/0.97  --qbf_dom_pre_inst                      false
% 2.76/0.97  --qbf_sk_in                             false
% 2.76/0.97  --qbf_pred_elim                         true
% 2.76/0.97  --qbf_split                             512
% 2.76/0.97  
% 2.76/0.97  ------ BMC1 Options
% 2.76/0.97  
% 2.76/0.97  --bmc1_incremental                      false
% 2.76/0.97  --bmc1_axioms                           reachable_all
% 2.76/0.97  --bmc1_min_bound                        0
% 2.76/0.97  --bmc1_max_bound                        -1
% 2.76/0.97  --bmc1_max_bound_default                -1
% 2.76/0.97  --bmc1_symbol_reachability              true
% 2.76/0.97  --bmc1_property_lemmas                  false
% 2.76/0.97  --bmc1_k_induction                      false
% 2.76/0.97  --bmc1_non_equiv_states                 false
% 2.76/0.97  --bmc1_deadlock                         false
% 2.76/0.97  --bmc1_ucm                              false
% 2.76/0.97  --bmc1_add_unsat_core                   none
% 2.76/0.97  --bmc1_unsat_core_children              false
% 2.76/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.97  --bmc1_out_stat                         full
% 2.76/0.97  --bmc1_ground_init                      false
% 2.76/0.97  --bmc1_pre_inst_next_state              false
% 2.76/0.97  --bmc1_pre_inst_state                   false
% 2.76/0.97  --bmc1_pre_inst_reach_state             false
% 2.76/0.97  --bmc1_out_unsat_core                   false
% 2.76/0.97  --bmc1_aig_witness_out                  false
% 2.76/0.97  --bmc1_verbose                          false
% 2.76/0.97  --bmc1_dump_clauses_tptp                false
% 2.76/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.97  --bmc1_dump_file                        -
% 2.76/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.97  --bmc1_ucm_extend_mode                  1
% 2.76/0.97  --bmc1_ucm_init_mode                    2
% 2.76/0.97  --bmc1_ucm_cone_mode                    none
% 2.76/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.97  --bmc1_ucm_relax_model                  4
% 2.76/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.97  --bmc1_ucm_layered_model                none
% 2.76/0.97  --bmc1_ucm_max_lemma_size               10
% 2.76/0.97  
% 2.76/0.97  ------ AIG Options
% 2.76/0.97  
% 2.76/0.97  --aig_mode                              false
% 2.76/0.97  
% 2.76/0.97  ------ Instantiation Options
% 2.76/0.97  
% 2.76/0.97  --instantiation_flag                    true
% 2.76/0.97  --inst_sos_flag                         false
% 2.76/0.97  --inst_sos_phase                        true
% 2.76/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.97  --inst_lit_sel_side                     none
% 2.76/0.97  --inst_solver_per_active                1400
% 2.76/0.97  --inst_solver_calls_frac                1.
% 2.76/0.97  --inst_passive_queue_type               priority_queues
% 2.76/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.97  --inst_passive_queues_freq              [25;2]
% 2.76/0.97  --inst_dismatching                      true
% 2.76/0.97  --inst_eager_unprocessed_to_passive     true
% 2.76/0.97  --inst_prop_sim_given                   true
% 2.76/0.97  --inst_prop_sim_new                     false
% 2.76/0.97  --inst_subs_new                         false
% 2.76/0.97  --inst_eq_res_simp                      false
% 2.76/0.97  --inst_subs_given                       false
% 2.76/0.97  --inst_orphan_elimination               true
% 2.76/0.97  --inst_learning_loop_flag               true
% 2.76/0.97  --inst_learning_start                   3000
% 2.76/0.97  --inst_learning_factor                  2
% 2.76/0.97  --inst_start_prop_sim_after_learn       3
% 2.76/0.97  --inst_sel_renew                        solver
% 2.76/0.97  --inst_lit_activity_flag                true
% 2.76/0.97  --inst_restr_to_given                   false
% 2.76/0.97  --inst_activity_threshold               500
% 2.76/0.97  --inst_out_proof                        true
% 2.76/0.97  
% 2.76/0.97  ------ Resolution Options
% 2.76/0.97  
% 2.76/0.97  --resolution_flag                       false
% 2.76/0.97  --res_lit_sel                           adaptive
% 2.76/0.97  --res_lit_sel_side                      none
% 2.76/0.97  --res_ordering                          kbo
% 2.76/0.97  --res_to_prop_solver                    active
% 2.76/0.97  --res_prop_simpl_new                    false
% 2.76/0.97  --res_prop_simpl_given                  true
% 2.76/0.97  --res_passive_queue_type                priority_queues
% 2.76/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.97  --res_passive_queues_freq               [15;5]
% 2.76/0.97  --res_forward_subs                      full
% 2.76/0.97  --res_backward_subs                     full
% 2.76/0.97  --res_forward_subs_resolution           true
% 2.76/0.97  --res_backward_subs_resolution          true
% 2.76/0.97  --res_orphan_elimination                true
% 2.76/0.97  --res_time_limit                        2.
% 2.76/0.97  --res_out_proof                         true
% 2.76/0.97  
% 2.76/0.97  ------ Superposition Options
% 2.76/0.97  
% 2.76/0.97  --superposition_flag                    true
% 2.76/0.97  --sup_passive_queue_type                priority_queues
% 2.76/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.97  --demod_completeness_check              fast
% 2.76/0.97  --demod_use_ground                      true
% 2.76/0.97  --sup_to_prop_solver                    passive
% 2.76/0.97  --sup_prop_simpl_new                    true
% 2.76/0.97  --sup_prop_simpl_given                  true
% 2.76/0.97  --sup_fun_splitting                     false
% 2.76/0.97  --sup_smt_interval                      50000
% 2.76/0.97  
% 2.76/0.97  ------ Superposition Simplification Setup
% 2.76/0.97  
% 2.76/0.97  --sup_indices_passive                   []
% 2.76/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_full_bw                           [BwDemod]
% 2.76/0.97  --sup_immed_triv                        [TrivRules]
% 2.76/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_immed_bw_main                     []
% 2.76/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.97  
% 2.76/0.97  ------ Combination Options
% 2.76/0.97  
% 2.76/0.97  --comb_res_mult                         3
% 2.76/0.97  --comb_sup_mult                         2
% 2.76/0.97  --comb_inst_mult                        10
% 2.76/0.97  
% 2.76/0.97  ------ Debug Options
% 2.76/0.97  
% 2.76/0.97  --dbg_backtrace                         false
% 2.76/0.97  --dbg_dump_prop_clauses                 false
% 2.76/0.97  --dbg_dump_prop_clauses_file            -
% 2.76/0.97  --dbg_out_stat                          false
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  ------ Proving...
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  % SZS status Theorem for theBenchmark.p
% 2.76/0.97  
% 2.76/0.97   Resolution empty clause
% 2.76/0.97  
% 2.76/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/0.97  
% 2.76/0.97  fof(f1,axiom,(
% 2.76/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f41,plain,(
% 2.76/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.76/0.97    inference(nnf_transformation,[],[f1])).
% 2.76/0.97  
% 2.76/0.97  fof(f42,plain,(
% 2.76/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.76/0.97    inference(rectify,[],[f41])).
% 2.76/0.97  
% 2.76/0.97  fof(f43,plain,(
% 2.76/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.76/0.97    introduced(choice_axiom,[])).
% 2.76/0.97  
% 2.76/0.97  fof(f44,plain,(
% 2.76/0.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.76/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 2.76/0.97  
% 2.76/0.97  fof(f65,plain,(
% 2.76/0.97    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f44])).
% 2.76/0.97  
% 2.76/0.97  fof(f13,axiom,(
% 2.76/0.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f96,plain,(
% 2.76/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.76/0.97    inference(cnf_transformation,[],[f13])).
% 2.76/0.97  
% 2.76/0.97  fof(f16,axiom,(
% 2.76/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f28,plain,(
% 2.76/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.76/0.97    inference(ennf_transformation,[],[f16])).
% 2.76/0.97  
% 2.76/0.97  fof(f99,plain,(
% 2.76/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f28])).
% 2.76/0.97  
% 2.76/0.97  fof(f21,conjecture,(
% 2.76/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f22,negated_conjecture,(
% 2.76/0.97    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.76/0.97    inference(negated_conjecture,[],[f21])).
% 2.76/0.97  
% 2.76/0.97  fof(f36,plain,(
% 2.76/0.97    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.76/0.97    inference(ennf_transformation,[],[f22])).
% 2.76/0.97  
% 2.76/0.97  fof(f37,plain,(
% 2.76/0.97    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.76/0.97    inference(flattening,[],[f36])).
% 2.76/0.97  
% 2.76/0.97  fof(f62,plain,(
% 2.76/0.97    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK7),X0) & m1_subset_1(sK7,X0))) )),
% 2.76/0.97    introduced(choice_axiom,[])).
% 2.76/0.97  
% 2.76/0.97  fof(f61,plain,(
% 2.76/0.97    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK6) & v1_subset_1(k6_domain_1(sK6,X1),sK6) & m1_subset_1(X1,sK6)) & ~v1_xboole_0(sK6))),
% 2.76/0.97    introduced(choice_axiom,[])).
% 2.76/0.97  
% 2.76/0.97  fof(f63,plain,(
% 2.76/0.97    (v1_zfmisc_1(sK6) & v1_subset_1(k6_domain_1(sK6,sK7),sK6) & m1_subset_1(sK7,sK6)) & ~v1_xboole_0(sK6)),
% 2.76/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f37,f62,f61])).
% 2.76/0.97  
% 2.76/0.97  fof(f104,plain,(
% 2.76/0.97    ~v1_xboole_0(sK6)),
% 2.76/0.97    inference(cnf_transformation,[],[f63])).
% 2.76/0.97  
% 2.76/0.97  fof(f105,plain,(
% 2.76/0.97    m1_subset_1(sK7,sK6)),
% 2.76/0.97    inference(cnf_transformation,[],[f63])).
% 2.76/0.97  
% 2.76/0.97  fof(f106,plain,(
% 2.76/0.97    v1_subset_1(k6_domain_1(sK6,sK7),sK6)),
% 2.76/0.97    inference(cnf_transformation,[],[f63])).
% 2.76/0.97  
% 2.76/0.97  fof(f20,axiom,(
% 2.76/0.97    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f34,plain,(
% 2.76/0.97    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.76/0.97    inference(ennf_transformation,[],[f20])).
% 2.76/0.97  
% 2.76/0.97  fof(f35,plain,(
% 2.76/0.97    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.76/0.97    inference(flattening,[],[f34])).
% 2.76/0.97  
% 2.76/0.97  fof(f103,plain,(
% 2.76/0.97    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f35])).
% 2.76/0.97  
% 2.76/0.97  fof(f14,axiom,(
% 2.76/0.97    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f25,plain,(
% 2.76/0.97    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.76/0.97    inference(ennf_transformation,[],[f14])).
% 2.76/0.97  
% 2.76/0.97  fof(f97,plain,(
% 2.76/0.97    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f25])).
% 2.76/0.97  
% 2.76/0.97  fof(f107,plain,(
% 2.76/0.97    v1_zfmisc_1(sK6)),
% 2.76/0.97    inference(cnf_transformation,[],[f63])).
% 2.76/0.97  
% 2.76/0.97  fof(f18,axiom,(
% 2.76/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f30,plain,(
% 2.76/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.76/0.97    inference(ennf_transformation,[],[f18])).
% 2.76/0.97  
% 2.76/0.97  fof(f31,plain,(
% 2.76/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.76/0.97    inference(flattening,[],[f30])).
% 2.76/0.97  
% 2.76/0.97  fof(f101,plain,(
% 2.76/0.97    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f31])).
% 2.76/0.97  
% 2.76/0.97  fof(f2,axiom,(
% 2.76/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f23,plain,(
% 2.76/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.76/0.97    inference(ennf_transformation,[],[f2])).
% 2.76/0.97  
% 2.76/0.97  fof(f45,plain,(
% 2.76/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.76/0.97    inference(nnf_transformation,[],[f23])).
% 2.76/0.97  
% 2.76/0.97  fof(f46,plain,(
% 2.76/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.76/0.97    inference(rectify,[],[f45])).
% 2.76/0.97  
% 2.76/0.97  fof(f47,plain,(
% 2.76/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.76/0.97    introduced(choice_axiom,[])).
% 2.76/0.97  
% 2.76/0.97  fof(f48,plain,(
% 2.76/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.76/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 2.76/0.97  
% 2.76/0.97  fof(f67,plain,(
% 2.76/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f48])).
% 2.76/0.97  
% 2.76/0.97  fof(f64,plain,(
% 2.76/0.97    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f44])).
% 2.76/0.97  
% 2.76/0.97  fof(f3,axiom,(
% 2.76/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f49,plain,(
% 2.76/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.76/0.97    inference(nnf_transformation,[],[f3])).
% 2.76/0.97  
% 2.76/0.97  fof(f50,plain,(
% 2.76/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.76/0.97    inference(flattening,[],[f49])).
% 2.76/0.97  
% 2.76/0.97  fof(f71,plain,(
% 2.76/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f50])).
% 2.76/0.97  
% 2.76/0.97  fof(f19,axiom,(
% 2.76/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f32,plain,(
% 2.76/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.76/0.97    inference(ennf_transformation,[],[f19])).
% 2.76/0.97  
% 2.76/0.97  fof(f33,plain,(
% 2.76/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.76/0.97    inference(flattening,[],[f32])).
% 2.76/0.97  
% 2.76/0.97  fof(f102,plain,(
% 2.76/0.97    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f33])).
% 2.76/0.97  
% 2.76/0.97  fof(f4,axiom,(
% 2.76/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f72,plain,(
% 2.76/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f4])).
% 2.76/0.97  
% 2.76/0.97  fof(f5,axiom,(
% 2.76/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f73,plain,(
% 2.76/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f5])).
% 2.76/0.97  
% 2.76/0.97  fof(f6,axiom,(
% 2.76/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f74,plain,(
% 2.76/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f6])).
% 2.76/0.97  
% 2.76/0.97  fof(f7,axiom,(
% 2.76/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f75,plain,(
% 2.76/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f7])).
% 2.76/0.97  
% 2.76/0.97  fof(f8,axiom,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f76,plain,(
% 2.76/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f8])).
% 2.76/0.97  
% 2.76/0.97  fof(f9,axiom,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f77,plain,(
% 2.76/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f9])).
% 2.76/0.97  
% 2.76/0.97  fof(f10,axiom,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f78,plain,(
% 2.76/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f10])).
% 2.76/0.97  
% 2.76/0.97  fof(f108,plain,(
% 2.76/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.76/0.97    inference(definition_unfolding,[],[f77,f78])).
% 2.76/0.97  
% 2.76/0.97  fof(f109,plain,(
% 2.76/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.76/0.97    inference(definition_unfolding,[],[f76,f108])).
% 2.76/0.97  
% 2.76/0.97  fof(f110,plain,(
% 2.76/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.76/0.97    inference(definition_unfolding,[],[f75,f109])).
% 2.76/0.97  
% 2.76/0.97  fof(f111,plain,(
% 2.76/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.76/0.97    inference(definition_unfolding,[],[f74,f110])).
% 2.76/0.97  
% 2.76/0.97  fof(f112,plain,(
% 2.76/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.76/0.97    inference(definition_unfolding,[],[f73,f111])).
% 2.76/0.97  
% 2.76/0.97  fof(f113,plain,(
% 2.76/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.76/0.97    inference(definition_unfolding,[],[f72,f112])).
% 2.76/0.97  
% 2.76/0.97  fof(f114,plain,(
% 2.76/0.97    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.76/0.97    inference(definition_unfolding,[],[f102,f113])).
% 2.76/0.97  
% 2.76/0.97  fof(f11,axiom,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 2.76/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.97  
% 2.76/0.97  fof(f24,plain,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 2.76/0.97    inference(ennf_transformation,[],[f11])).
% 2.76/0.97  
% 2.76/0.97  fof(f39,plain,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.76/0.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.76/0.97  
% 2.76/0.97  fof(f38,plain,(
% 2.76/0.97    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.76/0.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.76/0.97  
% 2.76/0.97  fof(f40,plain,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 2.76/0.97    inference(definition_folding,[],[f24,f39,f38])).
% 2.76/0.97  
% 2.76/0.97  fof(f58,plain,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 2.76/0.97    inference(nnf_transformation,[],[f40])).
% 2.76/0.97  
% 2.76/0.97  fof(f92,plain,(
% 2.76/0.97    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 2.76/0.97    inference(cnf_transformation,[],[f58])).
% 2.76/0.97  
% 2.76/0.97  fof(f125,plain,(
% 2.76/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.76/0.97    inference(equality_resolution,[],[f92])).
% 2.76/0.97  
% 2.76/0.97  fof(f55,plain,(
% 2.76/0.97    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.76/0.97    inference(nnf_transformation,[],[f38])).
% 2.76/0.97  
% 2.76/0.97  fof(f56,plain,(
% 2.76/0.97    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.76/0.97    inference(flattening,[],[f55])).
% 2.76/0.97  
% 2.76/0.97  fof(f57,plain,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.76/0.97    inference(rectify,[],[f56])).
% 2.76/0.97  
% 2.76/0.97  fof(f91,plain,(
% 2.76/0.97    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 2.76/0.97    inference(cnf_transformation,[],[f57])).
% 2.76/0.97  
% 2.76/0.97  fof(f117,plain,(
% 2.76/0.97    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.76/0.97    inference(equality_resolution,[],[f91])).
% 2.76/0.97  
% 2.76/0.97  fof(f51,plain,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.76/0.97    inference(nnf_transformation,[],[f39])).
% 2.76/0.97  
% 2.76/0.97  fof(f52,plain,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.76/0.97    inference(rectify,[],[f51])).
% 2.76/0.97  
% 2.76/0.97  fof(f53,plain,(
% 2.76/0.97    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 2.76/0.97    introduced(choice_axiom,[])).
% 2.76/0.97  
% 2.76/0.97  fof(f54,plain,(
% 2.76/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.76/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).
% 2.76/0.97  
% 2.76/0.97  fof(f80,plain,(
% 2.76/0.97    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.76/0.97    inference(cnf_transformation,[],[f54])).
% 2.76/0.97  
% 2.76/0.97  cnf(c_0,plain,
% 2.76/0.97      ( r2_hidden(sK2(X0),X0) | v1_xboole_0(X0) ),
% 2.76/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2700,plain,
% 2.76/0.97      ( r2_hidden(sK2(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_25,plain,
% 2.76/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.76/0.97      inference(cnf_transformation,[],[f96]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2676,plain,
% 2.76/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_28,plain,
% 2.76/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/0.97      | ~ r2_hidden(X2,X0)
% 2.76/0.97      | ~ v1_xboole_0(X1) ),
% 2.76/0.97      inference(cnf_transformation,[],[f99]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2674,plain,
% 2.76/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.76/0.97      | r2_hidden(X2,X0) != iProver_top
% 2.76/0.97      | v1_xboole_0(X1) != iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_4396,plain,
% 2.76/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.76/0.97      | v1_xboole_0(X1) != iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_2676,c_2674]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_36,negated_conjecture,
% 2.76/0.97      ( ~ v1_xboole_0(sK6) ),
% 2.76/0.97      inference(cnf_transformation,[],[f104]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_37,plain,
% 2.76/0.97      ( v1_xboole_0(sK6) != iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_35,negated_conjecture,
% 2.76/0.97      ( m1_subset_1(sK7,sK6) ),
% 2.76/0.97      inference(cnf_transformation,[],[f105]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_38,plain,
% 2.76/0.97      ( m1_subset_1(sK7,sK6) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_34,negated_conjecture,
% 2.76/0.97      ( v1_subset_1(k6_domain_1(sK6,sK7),sK6) ),
% 2.76/0.97      inference(cnf_transformation,[],[f106]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_32,plain,
% 2.76/0.97      ( ~ v1_subset_1(X0,X1)
% 2.76/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/0.97      | ~ v1_zfmisc_1(X1)
% 2.76/0.97      | v1_xboole_0(X1)
% 2.76/0.97      | v1_xboole_0(X0) ),
% 2.76/0.97      inference(cnf_transformation,[],[f103]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_26,plain,
% 2.76/0.97      ( ~ v1_subset_1(X0,X1)
% 2.76/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/0.97      | ~ v1_xboole_0(X1) ),
% 2.76/0.97      inference(cnf_transformation,[],[f97]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_189,plain,
% 2.76/0.97      ( ~ v1_zfmisc_1(X1)
% 2.76/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/0.97      | ~ v1_subset_1(X0,X1)
% 2.76/0.97      | v1_xboole_0(X0) ),
% 2.76/0.97      inference(global_propositional_subsumption,[status(thm)],[c_32,c_26]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_190,plain,
% 2.76/0.97      ( ~ v1_subset_1(X0,X1)
% 2.76/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/0.97      | ~ v1_zfmisc_1(X1)
% 2.76/0.97      | v1_xboole_0(X0) ),
% 2.76/0.97      inference(renaming,[status(thm)],[c_189]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_33,negated_conjecture,
% 2.76/0.97      ( v1_zfmisc_1(sK6) ),
% 2.76/0.97      inference(cnf_transformation,[],[f107]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_386,plain,
% 2.76/0.97      ( ~ v1_subset_1(X0,X1)
% 2.76/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.76/0.97      | v1_xboole_0(X0)
% 2.76/0.97      | sK6 != X1 ),
% 2.76/0.97      inference(resolution_lifted,[status(thm)],[c_190,c_33]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_387,plain,
% 2.76/0.97      ( ~ v1_subset_1(X0,sK6)
% 2.76/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(sK6))
% 2.76/0.97      | v1_xboole_0(X0) ),
% 2.76/0.97      inference(unflattening,[status(thm)],[c_386]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_407,plain,
% 2.76/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6))
% 2.76/0.97      | v1_xboole_0(X0)
% 2.76/0.97      | k6_domain_1(sK6,sK7) != X0
% 2.76/0.97      | sK6 != sK6 ),
% 2.76/0.97      inference(resolution_lifted,[status(thm)],[c_34,c_387]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_408,plain,
% 2.76/0.97      ( ~ m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6))
% 2.76/0.97      | v1_xboole_0(k6_domain_1(sK6,sK7)) ),
% 2.76/0.97      inference(unflattening,[status(thm)],[c_407]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_409,plain,
% 2.76/0.97      ( m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 2.76/0.97      | v1_xboole_0(k6_domain_1(sK6,sK7)) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_30,plain,
% 2.76/0.97      ( ~ m1_subset_1(X0,X1)
% 2.76/0.97      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.76/0.97      | v1_xboole_0(X1) ),
% 2.76/0.97      inference(cnf_transformation,[],[f101]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2940,plain,
% 2.76/0.97      ( m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6))
% 2.76/0.97      | ~ m1_subset_1(sK7,sK6)
% 2.76/0.97      | v1_xboole_0(sK6) ),
% 2.76/0.97      inference(instantiation,[status(thm)],[c_30]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2941,plain,
% 2.76/0.97      ( m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6)) = iProver_top
% 2.76/0.97      | m1_subset_1(sK7,sK6) != iProver_top
% 2.76/0.97      | v1_xboole_0(sK6) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_2940]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_3057,plain,
% 2.76/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k6_domain_1(sK6,sK7)))
% 2.76/0.97      | ~ r2_hidden(X1,X0)
% 2.76/0.97      | ~ v1_xboole_0(k6_domain_1(sK6,sK7)) ),
% 2.76/0.97      inference(instantiation,[status(thm)],[c_28]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_3272,plain,
% 2.76/0.97      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k6_domain_1(sK6,sK7)))
% 2.76/0.97      | ~ r2_hidden(X0,k1_xboole_0)
% 2.76/0.97      | ~ v1_xboole_0(k6_domain_1(sK6,sK7)) ),
% 2.76/0.97      inference(instantiation,[status(thm)],[c_3057]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_3274,plain,
% 2.76/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k6_domain_1(sK6,sK7))) != iProver_top
% 2.76/0.97      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.76/0.97      | v1_xboole_0(k6_domain_1(sK6,sK7)) != iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_3272]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_3273,plain,
% 2.76/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k6_domain_1(sK6,sK7))) ),
% 2.76/0.97      inference(instantiation,[status(thm)],[c_25]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_3278,plain,
% 2.76/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k6_domain_1(sK6,sK7))) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_3273]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_8062,plain,
% 2.76/0.97      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.76/0.97      inference(global_propositional_subsumption,
% 2.76/0.97                [status(thm)],
% 2.76/0.97                [c_4396,c_37,c_38,c_409,c_2941,c_3274,c_3278]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_8069,plain,
% 2.76/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_2700,c_8062]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2668,plain,
% 2.76/0.97      ( m1_subset_1(k6_domain_1(sK6,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 2.76/0.97      | v1_xboole_0(k6_domain_1(sK6,sK7)) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2977,plain,
% 2.76/0.97      ( v1_xboole_0(k6_domain_1(sK6,sK7)) = iProver_top ),
% 2.76/0.97      inference(global_propositional_subsumption,
% 2.76/0.97                [status(thm)],
% 2.76/0.97                [c_2668,c_37,c_38,c_409,c_2941]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_3,plain,
% 2.76/0.97      ( r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0) ),
% 2.76/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2697,plain,
% 2.76/0.97      ( r1_tarski(X0,X1) = iProver_top
% 2.76/0.97      | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_1,plain,
% 2.76/0.97      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.76/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2699,plain,
% 2.76/0.97      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_3836,plain,
% 2.76/0.97      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_2697,c_2699]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_5,plain,
% 2.76/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.76/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2695,plain,
% 2.76/0.97      ( X0 = X1
% 2.76/0.97      | r1_tarski(X1,X0) != iProver_top
% 2.76/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_4147,plain,
% 2.76/0.97      ( X0 = X1
% 2.76/0.97      | r1_tarski(X0,X1) != iProver_top
% 2.76/0.97      | v1_xboole_0(X1) != iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_3836,c_2695]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_4163,plain,
% 2.76/0.97      ( X0 = X1
% 2.76/0.97      | v1_xboole_0(X0) != iProver_top
% 2.76/0.97      | v1_xboole_0(X1) != iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_3836,c_4147]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_4238,plain,
% 2.76/0.97      ( k6_domain_1(sK6,sK7) = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_2977,c_4163]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_8224,plain,
% 2.76/0.97      ( k6_domain_1(sK6,sK7) = k1_xboole_0 ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_8069,c_4238]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2670,plain,
% 2.76/0.97      ( m1_subset_1(sK7,sK6) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_31,plain,
% 2.76/0.97      ( ~ m1_subset_1(X0,X1)
% 2.76/0.97      | v1_xboole_0(X1)
% 2.76/0.97      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.76/0.97      inference(cnf_transformation,[],[f114]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2671,plain,
% 2.76/0.97      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
% 2.76/0.97      | m1_subset_1(X0,X1) != iProver_top
% 2.76/0.97      | v1_xboole_0(X1) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_3128,plain,
% 2.76/0.97      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(sK6,sK7)
% 2.76/0.97      | v1_xboole_0(sK6) = iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_2670,c_2671]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2968,plain,
% 2.76/0.97      ( ~ m1_subset_1(sK7,sK6)
% 2.76/0.97      | v1_xboole_0(sK6)
% 2.76/0.97      | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(sK6,sK7) ),
% 2.76/0.97      inference(instantiation,[status(thm)],[c_31]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_3453,plain,
% 2.76/0.97      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(sK6,sK7) ),
% 2.76/0.97      inference(global_propositional_subsumption,
% 2.76/0.97                [status(thm)],
% 2.76/0.97                [c_3128,c_36,c_35,c_2968]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_22,plain,
% 2.76/0.97      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.76/0.97      inference(cnf_transformation,[],[f125]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2679,plain,
% 2.76/0.97      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_4646,plain,
% 2.76/0.97      ( sP1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7,k6_domain_1(sK6,sK7)) = iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_3453,c_2679]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_8243,plain,
% 2.76/0.97      ( sP1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7,k1_xboole_0) = iProver_top ),
% 2.76/0.97      inference(demodulation,[status(thm)],[c_8224,c_4646]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_12,plain,
% 2.76/0.97      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 2.76/0.97      inference(cnf_transformation,[],[f117]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2689,plain,
% 2.76/0.97      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_10,plain,
% 2.76/0.97      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.76/0.97      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 2.76/0.97      | r2_hidden(X0,X9) ),
% 2.76/0.97      inference(cnf_transformation,[],[f80]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_2691,plain,
% 2.76/0.97      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.76/0.97      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 2.76/0.97      | r2_hidden(X0,X9) = iProver_top ),
% 2.76/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_5606,plain,
% 2.76/0.97      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.76/0.97      | r2_hidden(X7,X8) = iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_2689,c_2691]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_9515,plain,
% 2.76/0.97      ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
% 2.76/0.97      inference(superposition,[status(thm)],[c_8243,c_5606]) ).
% 2.76/0.97  
% 2.76/0.97  cnf(c_9756,plain,
% 2.76/0.97      ( $false ),
% 2.76/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_9515,c_8062]) ).
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/0.97  
% 2.76/0.97  ------                               Statistics
% 2.76/0.97  
% 2.76/0.97  ------ General
% 2.76/0.97  
% 2.76/0.97  abstr_ref_over_cycles:                  0
% 2.76/0.97  abstr_ref_under_cycles:                 0
% 2.76/0.97  gc_basic_clause_elim:                   0
% 2.76/0.97  forced_gc_time:                         0
% 2.76/0.97  parsing_time:                           0.009
% 2.76/0.97  unif_index_cands_time:                  0.
% 2.76/0.97  unif_index_add_time:                    0.
% 2.76/0.97  orderings_time:                         0.
% 2.76/0.97  out_proof_time:                         0.008
% 2.76/0.97  total_time:                             0.285
% 2.76/0.97  num_of_symbols:                         49
% 2.76/0.97  num_of_terms:                           9029
% 2.76/0.97  
% 2.76/0.97  ------ Preprocessing
% 2.76/0.97  
% 2.76/0.97  num_of_splits:                          0
% 2.76/0.97  num_of_split_atoms:                     0
% 2.76/0.97  num_of_reused_defs:                     0
% 2.76/0.97  num_eq_ax_congr_red:                    121
% 2.76/0.97  num_of_sem_filtered_clauses:            1
% 2.76/0.97  num_of_subtypes:                        0
% 2.76/0.97  monotx_restored_types:                  0
% 2.76/0.97  sat_num_of_epr_types:                   0
% 2.76/0.97  sat_num_of_non_cyclic_types:            0
% 2.76/0.97  sat_guarded_non_collapsed_types:        0
% 2.76/0.97  num_pure_diseq_elim:                    0
% 2.76/0.97  simp_replaced_by:                       0
% 2.76/0.97  res_preprocessed:                       154
% 2.76/0.97  prep_upred:                             0
% 2.76/0.97  prep_unflattend:                        618
% 2.76/0.97  smt_new_axioms:                         0
% 2.76/0.97  pred_elim_cands:                        6
% 2.76/0.97  pred_elim:                              2
% 2.76/0.97  pred_elim_cl:                           3
% 2.76/0.97  pred_elim_cycles:                       8
% 2.76/0.97  merged_defs:                            0
% 2.76/0.97  merged_defs_ncl:                        0
% 2.76/0.97  bin_hyper_res:                          0
% 2.76/0.97  prep_cycles:                            4
% 2.76/0.97  pred_elim_time:                         0.037
% 2.76/0.97  splitting_time:                         0.
% 2.76/0.97  sem_filter_time:                        0.
% 2.76/0.97  monotx_time:                            0.001
% 2.76/0.97  subtype_inf_time:                       0.
% 2.76/0.97  
% 2.76/0.97  ------ Problem properties
% 2.76/0.97  
% 2.76/0.97  clauses:                                33
% 2.76/0.97  conjectures:                            2
% 2.76/0.97  epr:                                    18
% 2.76/0.97  horn:                                   27
% 2.76/0.97  ground:                                 3
% 2.76/0.97  unary:                                  15
% 2.76/0.97  binary:                                 7
% 2.76/0.97  lits:                                   68
% 2.76/0.97  lits_eq:                                11
% 2.76/0.97  fd_pure:                                0
% 2.76/0.97  fd_pseudo:                              0
% 2.76/0.97  fd_cond:                                0
% 2.76/0.97  fd_pseudo_cond:                         3
% 2.76/0.97  ac_symbols:                             0
% 2.76/0.97  
% 2.76/0.97  ------ Propositional Solver
% 2.76/0.97  
% 2.76/0.97  prop_solver_calls:                      27
% 2.76/0.97  prop_fast_solver_calls:                 1116
% 2.76/0.97  smt_solver_calls:                       0
% 2.76/0.97  smt_fast_solver_calls:                  0
% 2.76/0.97  prop_num_of_clauses:                    2997
% 2.76/0.97  prop_preprocess_simplified:             11241
% 2.76/0.97  prop_fo_subsumed:                       10
% 2.76/0.97  prop_solver_time:                       0.
% 2.76/0.97  smt_solver_time:                        0.
% 2.76/0.97  smt_fast_solver_time:                   0.
% 2.76/0.97  prop_fast_solver_time:                  0.
% 2.76/0.97  prop_unsat_core_time:                   0.
% 2.76/0.97  
% 2.76/0.97  ------ QBF
% 2.76/0.97  
% 2.76/0.97  qbf_q_res:                              0
% 2.76/0.97  qbf_num_tautologies:                    0
% 2.76/0.97  qbf_prep_cycles:                        0
% 2.76/0.97  
% 2.76/0.97  ------ BMC1
% 2.76/0.97  
% 2.76/0.97  bmc1_current_bound:                     -1
% 2.76/0.97  bmc1_last_solved_bound:                 -1
% 2.76/0.97  bmc1_unsat_core_size:                   -1
% 2.76/0.97  bmc1_unsat_core_parents_size:           -1
% 2.76/0.97  bmc1_merge_next_fun:                    0
% 2.76/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.76/0.97  
% 2.76/0.97  ------ Instantiation
% 2.76/0.97  
% 2.76/0.97  inst_num_of_clauses:                    909
% 2.76/0.97  inst_num_in_passive:                    346
% 2.76/0.97  inst_num_in_active:                     370
% 2.76/0.97  inst_num_in_unprocessed:                193
% 2.76/0.97  inst_num_of_loops:                      400
% 2.76/0.97  inst_num_of_learning_restarts:          0
% 2.76/0.97  inst_num_moves_active_passive:          29
% 2.76/0.97  inst_lit_activity:                      0
% 2.76/0.97  inst_lit_activity_moves:                0
% 2.76/0.97  inst_num_tautologies:                   0
% 2.76/0.97  inst_num_prop_implied:                  0
% 2.76/0.97  inst_num_existing_simplified:           0
% 2.76/0.97  inst_num_eq_res_simplified:             0
% 2.76/0.97  inst_num_child_elim:                    0
% 2.76/0.97  inst_num_of_dismatching_blockings:      409
% 2.76/0.97  inst_num_of_non_proper_insts:           809
% 2.76/0.97  inst_num_of_duplicates:                 0
% 2.76/0.97  inst_inst_num_from_inst_to_res:         0
% 2.76/0.97  inst_dismatching_checking_time:         0.
% 2.76/0.97  
% 2.76/0.97  ------ Resolution
% 2.76/0.97  
% 2.76/0.97  res_num_of_clauses:                     0
% 2.76/0.97  res_num_in_passive:                     0
% 2.76/0.97  res_num_in_active:                      0
% 2.76/0.97  res_num_of_loops:                       158
% 2.76/0.97  res_forward_subset_subsumed:            167
% 2.76/0.97  res_backward_subset_subsumed:           0
% 2.76/0.97  res_forward_subsumed:                   0
% 2.76/0.97  res_backward_subsumed:                  0
% 2.76/0.97  res_forward_subsumption_resolution:     0
% 2.76/0.97  res_backward_subsumption_resolution:    0
% 2.76/0.97  res_clause_to_clause_subsumption:       1252
% 2.76/0.97  res_orphan_elimination:                 0
% 2.76/0.97  res_tautology_del:                      108
% 2.76/0.97  res_num_eq_res_simplified:              0
% 2.76/0.97  res_num_sel_changes:                    0
% 2.76/0.97  res_moves_from_active_to_pass:          0
% 2.76/0.97  
% 2.76/0.97  ------ Superposition
% 2.76/0.97  
% 2.76/0.97  sup_time_total:                         0.
% 2.76/0.97  sup_time_generating:                    0.
% 2.76/0.97  sup_time_sim_full:                      0.
% 2.76/0.97  sup_time_sim_immed:                     0.
% 2.76/0.97  
% 2.76/0.97  sup_num_of_clauses:                     137
% 2.76/0.97  sup_num_in_active:                      63
% 2.76/0.97  sup_num_in_passive:                     74
% 2.76/0.97  sup_num_of_loops:                       79
% 2.76/0.97  sup_fw_superposition:                   297
% 2.76/0.97  sup_bw_superposition:                   130
% 2.76/0.97  sup_immediate_simplified:               37
% 2.76/0.97  sup_given_eliminated:                   5
% 2.76/0.97  comparisons_done:                       0
% 2.76/0.97  comparisons_avoided:                    18
% 2.76/0.97  
% 2.76/0.97  ------ Simplifications
% 2.76/0.97  
% 2.76/0.97  
% 2.76/0.97  sim_fw_subset_subsumed:                 12
% 2.76/0.97  sim_bw_subset_subsumed:                 1
% 2.76/0.97  sim_fw_subsumed:                        16
% 2.76/0.97  sim_bw_subsumed:                        6
% 2.76/0.97  sim_fw_subsumption_res:                 1
% 2.76/0.97  sim_bw_subsumption_res:                 0
% 2.76/0.97  sim_tautology_del:                      3
% 2.76/0.97  sim_eq_tautology_del:                   10
% 2.76/0.97  sim_eq_res_simp:                        0
% 2.76/0.97  sim_fw_demodulated:                     1
% 2.76/0.97  sim_bw_demodulated:                     11
% 2.76/0.97  sim_light_normalised:                   17
% 2.76/0.97  sim_joinable_taut:                      0
% 2.76/0.97  sim_joinable_simp:                      0
% 2.76/0.97  sim_ac_normalised:                      0
% 2.76/0.97  sim_smt_subsumption:                    0
% 2.76/0.97  
%------------------------------------------------------------------------------
