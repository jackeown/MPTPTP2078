%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:06 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 203 expanded)
%              Number of clauses        :   49 (  62 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :   19
%              Number of atoms          :  378 ( 695 expanded)
%              Number of equality atoms :  151 ( 163 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK4),X0)
        & m1_subset_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK3)
          & v1_subset_1(k6_domain_1(sK3,X1),sK3)
          & m1_subset_1(X1,sK3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( v1_zfmisc_1(sK3)
    & v1_subset_1(k6_domain_1(sK3,sK4),sK3)
    & m1_subset_1(sK4,sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f49,f48])).

fof(f84,plain,(
    m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f87])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f88])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f89])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f90])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f91])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f81,f92])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,(
    v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f37,plain,(
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

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f23,f38,f37])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f73])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f72])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2297,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2298,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3320,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(sK3,sK4)
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2297,c_2298])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2318,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_26,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_24,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_18,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_149,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_18])).

cnf(c_150,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_25,negated_conjecture,
    ( v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_321,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_150,c_25])).

cnf(c_322,plain,
    ( ~ v1_subset_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | v1_xboole_0(X0)
    | k6_domain_1(sK3,sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_322])).

cnf(c_343,plain,
    ( ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
    | v1_xboole_0(k6_domain_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_2294,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_344,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2496,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2497,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2496])).

cnf(c_2522,plain,
    ( v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2294,c_29,c_30,c_344,c_2497])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2317,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2973,plain,
    ( k6_domain_1(sK3,sK4) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2522,c_2317])).

cnf(c_3069,plain,
    ( k6_domain_1(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2318,c_2973])).

cnf(c_3323,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3320,c_3069])).

cnf(c_3707,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3323,c_29])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2302,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3710,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3707,c_2302])).

cnf(c_6,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2312,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2314,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3922,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_2314])).

cnf(c_4189,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3710,c_3922])).

cnf(c_17,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2301,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_19,c_21])).

cnf(c_2295,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_2641,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2301,c_2295])).

cnf(c_4200,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4189,c_2641])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.79/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.00  
% 2.79/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/1.00  
% 2.79/1.00  ------  iProver source info
% 2.79/1.00  
% 2.79/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.79/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/1.00  git: non_committed_changes: false
% 2.79/1.00  git: last_make_outside_of_git: false
% 2.79/1.00  
% 2.79/1.00  ------ 
% 2.79/1.00  
% 2.79/1.00  ------ Input Options
% 2.79/1.00  
% 2.79/1.00  --out_options                           all
% 2.79/1.00  --tptp_safe_out                         true
% 2.79/1.00  --problem_path                          ""
% 2.79/1.00  --include_path                          ""
% 2.79/1.00  --clausifier                            res/vclausify_rel
% 2.79/1.00  --clausifier_options                    --mode clausify
% 2.79/1.00  --stdin                                 false
% 2.79/1.00  --stats_out                             all
% 2.79/1.00  
% 2.79/1.00  ------ General Options
% 2.79/1.00  
% 2.79/1.00  --fof                                   false
% 2.79/1.00  --time_out_real                         305.
% 2.79/1.00  --time_out_virtual                      -1.
% 2.79/1.00  --symbol_type_check                     false
% 2.79/1.00  --clausify_out                          false
% 2.79/1.00  --sig_cnt_out                           false
% 2.79/1.00  --trig_cnt_out                          false
% 2.79/1.00  --trig_cnt_out_tolerance                1.
% 2.79/1.00  --trig_cnt_out_sk_spl                   false
% 2.79/1.00  --abstr_cl_out                          false
% 2.79/1.00  
% 2.79/1.00  ------ Global Options
% 2.79/1.00  
% 2.79/1.00  --schedule                              default
% 2.79/1.00  --add_important_lit                     false
% 2.79/1.00  --prop_solver_per_cl                    1000
% 2.79/1.00  --min_unsat_core                        false
% 2.79/1.00  --soft_assumptions                      false
% 2.79/1.00  --soft_lemma_size                       3
% 2.79/1.00  --prop_impl_unit_size                   0
% 2.79/1.00  --prop_impl_unit                        []
% 2.79/1.00  --share_sel_clauses                     true
% 2.79/1.00  --reset_solvers                         false
% 2.79/1.00  --bc_imp_inh                            [conj_cone]
% 2.79/1.00  --conj_cone_tolerance                   3.
% 2.79/1.00  --extra_neg_conj                        none
% 2.79/1.00  --large_theory_mode                     true
% 2.79/1.00  --prolific_symb_bound                   200
% 2.79/1.00  --lt_threshold                          2000
% 2.79/1.00  --clause_weak_htbl                      true
% 2.79/1.00  --gc_record_bc_elim                     false
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing Options
% 2.79/1.00  
% 2.79/1.00  --preprocessing_flag                    true
% 2.79/1.00  --time_out_prep_mult                    0.1
% 2.79/1.00  --splitting_mode                        input
% 2.79/1.00  --splitting_grd                         true
% 2.79/1.00  --splitting_cvd                         false
% 2.79/1.00  --splitting_cvd_svl                     false
% 2.79/1.00  --splitting_nvd                         32
% 2.79/1.00  --sub_typing                            true
% 2.79/1.00  --prep_gs_sim                           true
% 2.79/1.00  --prep_unflatten                        true
% 2.79/1.00  --prep_res_sim                          true
% 2.79/1.00  --prep_upred                            true
% 2.79/1.00  --prep_sem_filter                       exhaustive
% 2.79/1.00  --prep_sem_filter_out                   false
% 2.79/1.00  --pred_elim                             true
% 2.79/1.00  --res_sim_input                         true
% 2.79/1.00  --eq_ax_congr_red                       true
% 2.79/1.00  --pure_diseq_elim                       true
% 2.79/1.00  --brand_transform                       false
% 2.79/1.00  --non_eq_to_eq                          false
% 2.79/1.00  --prep_def_merge                        true
% 2.79/1.00  --prep_def_merge_prop_impl              false
% 2.79/1.00  --prep_def_merge_mbd                    true
% 2.79/1.00  --prep_def_merge_tr_red                 false
% 2.79/1.00  --prep_def_merge_tr_cl                  false
% 2.79/1.00  --smt_preprocessing                     true
% 2.79/1.00  --smt_ac_axioms                         fast
% 2.79/1.00  --preprocessed_out                      false
% 2.79/1.00  --preprocessed_stats                    false
% 2.79/1.00  
% 2.79/1.00  ------ Abstraction refinement Options
% 2.79/1.00  
% 2.79/1.00  --abstr_ref                             []
% 2.79/1.00  --abstr_ref_prep                        false
% 2.79/1.00  --abstr_ref_until_sat                   false
% 2.79/1.00  --abstr_ref_sig_restrict                funpre
% 2.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/1.00  --abstr_ref_under                       []
% 2.79/1.00  
% 2.79/1.00  ------ SAT Options
% 2.79/1.00  
% 2.79/1.00  --sat_mode                              false
% 2.79/1.00  --sat_fm_restart_options                ""
% 2.79/1.00  --sat_gr_def                            false
% 2.79/1.00  --sat_epr_types                         true
% 2.79/1.00  --sat_non_cyclic_types                  false
% 2.79/1.00  --sat_finite_models                     false
% 2.79/1.00  --sat_fm_lemmas                         false
% 2.79/1.00  --sat_fm_prep                           false
% 2.79/1.00  --sat_fm_uc_incr                        true
% 2.79/1.00  --sat_out_model                         small
% 2.79/1.00  --sat_out_clauses                       false
% 2.79/1.00  
% 2.79/1.00  ------ QBF Options
% 2.79/1.00  
% 2.79/1.00  --qbf_mode                              false
% 2.79/1.00  --qbf_elim_univ                         false
% 2.79/1.00  --qbf_dom_inst                          none
% 2.79/1.00  --qbf_dom_pre_inst                      false
% 2.79/1.00  --qbf_sk_in                             false
% 2.79/1.00  --qbf_pred_elim                         true
% 2.79/1.00  --qbf_split                             512
% 2.79/1.00  
% 2.79/1.00  ------ BMC1 Options
% 2.79/1.00  
% 2.79/1.00  --bmc1_incremental                      false
% 2.79/1.00  --bmc1_axioms                           reachable_all
% 2.79/1.00  --bmc1_min_bound                        0
% 2.79/1.00  --bmc1_max_bound                        -1
% 2.79/1.00  --bmc1_max_bound_default                -1
% 2.79/1.00  --bmc1_symbol_reachability              true
% 2.79/1.00  --bmc1_property_lemmas                  false
% 2.79/1.00  --bmc1_k_induction                      false
% 2.79/1.00  --bmc1_non_equiv_states                 false
% 2.79/1.00  --bmc1_deadlock                         false
% 2.79/1.00  --bmc1_ucm                              false
% 2.79/1.00  --bmc1_add_unsat_core                   none
% 2.79/1.00  --bmc1_unsat_core_children              false
% 2.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/1.00  --bmc1_out_stat                         full
% 2.79/1.00  --bmc1_ground_init                      false
% 2.79/1.00  --bmc1_pre_inst_next_state              false
% 2.79/1.00  --bmc1_pre_inst_state                   false
% 2.79/1.00  --bmc1_pre_inst_reach_state             false
% 2.79/1.00  --bmc1_out_unsat_core                   false
% 2.79/1.00  --bmc1_aig_witness_out                  false
% 2.79/1.00  --bmc1_verbose                          false
% 2.79/1.00  --bmc1_dump_clauses_tptp                false
% 2.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.79/1.00  --bmc1_dump_file                        -
% 2.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.79/1.00  --bmc1_ucm_extend_mode                  1
% 2.79/1.00  --bmc1_ucm_init_mode                    2
% 2.79/1.00  --bmc1_ucm_cone_mode                    none
% 2.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.79/1.00  --bmc1_ucm_relax_model                  4
% 2.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/1.00  --bmc1_ucm_layered_model                none
% 2.79/1.00  --bmc1_ucm_max_lemma_size               10
% 2.79/1.00  
% 2.79/1.00  ------ AIG Options
% 2.79/1.00  
% 2.79/1.00  --aig_mode                              false
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation Options
% 2.79/1.00  
% 2.79/1.00  --instantiation_flag                    true
% 2.79/1.00  --inst_sos_flag                         false
% 2.79/1.00  --inst_sos_phase                        true
% 2.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel_side                     num_symb
% 2.79/1.00  --inst_solver_per_active                1400
% 2.79/1.00  --inst_solver_calls_frac                1.
% 2.79/1.00  --inst_passive_queue_type               priority_queues
% 2.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/1.00  --inst_passive_queues_freq              [25;2]
% 2.79/1.00  --inst_dismatching                      true
% 2.79/1.00  --inst_eager_unprocessed_to_passive     true
% 2.79/1.00  --inst_prop_sim_given                   true
% 2.79/1.00  --inst_prop_sim_new                     false
% 2.79/1.00  --inst_subs_new                         false
% 2.79/1.00  --inst_eq_res_simp                      false
% 2.79/1.00  --inst_subs_given                       false
% 2.79/1.00  --inst_orphan_elimination               true
% 2.79/1.00  --inst_learning_loop_flag               true
% 2.79/1.00  --inst_learning_start                   3000
% 2.79/1.00  --inst_learning_factor                  2
% 2.79/1.00  --inst_start_prop_sim_after_learn       3
% 2.79/1.00  --inst_sel_renew                        solver
% 2.79/1.00  --inst_lit_activity_flag                true
% 2.79/1.00  --inst_restr_to_given                   false
% 2.79/1.00  --inst_activity_threshold               500
% 2.79/1.00  --inst_out_proof                        true
% 2.79/1.00  
% 2.79/1.00  ------ Resolution Options
% 2.79/1.00  
% 2.79/1.00  --resolution_flag                       true
% 2.79/1.00  --res_lit_sel                           adaptive
% 2.79/1.00  --res_lit_sel_side                      none
% 2.79/1.00  --res_ordering                          kbo
% 2.79/1.00  --res_to_prop_solver                    active
% 2.79/1.00  --res_prop_simpl_new                    false
% 2.79/1.00  --res_prop_simpl_given                  true
% 2.79/1.00  --res_passive_queue_type                priority_queues
% 2.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/1.00  --res_passive_queues_freq               [15;5]
% 2.79/1.00  --res_forward_subs                      full
% 2.79/1.00  --res_backward_subs                     full
% 2.79/1.00  --res_forward_subs_resolution           true
% 2.79/1.00  --res_backward_subs_resolution          true
% 2.79/1.00  --res_orphan_elimination                true
% 2.79/1.00  --res_time_limit                        2.
% 2.79/1.00  --res_out_proof                         true
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Options
% 2.79/1.00  
% 2.79/1.00  --superposition_flag                    true
% 2.79/1.00  --sup_passive_queue_type                priority_queues
% 2.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.79/1.00  --demod_completeness_check              fast
% 2.79/1.00  --demod_use_ground                      true
% 2.79/1.00  --sup_to_prop_solver                    passive
% 2.79/1.00  --sup_prop_simpl_new                    true
% 2.79/1.00  --sup_prop_simpl_given                  true
% 2.79/1.00  --sup_fun_splitting                     false
% 2.79/1.00  --sup_smt_interval                      50000
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Simplification Setup
% 2.79/1.00  
% 2.79/1.00  --sup_indices_passive                   []
% 2.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_full_bw                           [BwDemod]
% 2.79/1.00  --sup_immed_triv                        [TrivRules]
% 2.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_immed_bw_main                     []
% 2.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  
% 2.79/1.00  ------ Combination Options
% 2.79/1.00  
% 2.79/1.00  --comb_res_mult                         3
% 2.79/1.00  --comb_sup_mult                         2
% 2.79/1.00  --comb_inst_mult                        10
% 2.79/1.00  
% 2.79/1.00  ------ Debug Options
% 2.79/1.00  
% 2.79/1.00  --dbg_backtrace                         false
% 2.79/1.00  --dbg_dump_prop_clauses                 false
% 2.79/1.00  --dbg_dump_prop_clauses_file            -
% 2.79/1.00  --dbg_out_stat                          false
% 2.79/1.00  ------ Parsing...
% 2.79/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/1.00  ------ Proving...
% 2.79/1.00  ------ Problem Properties 
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  clauses                                 25
% 2.79/1.00  conjectures                             2
% 2.79/1.00  EPR                                     15
% 2.79/1.00  Horn                                    21
% 2.79/1.00  unary                                   13
% 2.79/1.00  binary                                  3
% 2.79/1.00  lits                                    52
% 2.79/1.00  lits eq                                 11
% 2.79/1.00  fd_pure                                 0
% 2.79/1.00  fd_pseudo                               0
% 2.79/1.00  fd_cond                                 0
% 2.79/1.00  fd_pseudo_cond                          3
% 2.79/1.00  AC symbols                              0
% 2.79/1.00  
% 2.79/1.00  ------ Schedule dynamic 5 is on 
% 2.79/1.00  
% 2.79/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  ------ 
% 2.79/1.00  Current options:
% 2.79/1.00  ------ 
% 2.79/1.00  
% 2.79/1.00  ------ Input Options
% 2.79/1.00  
% 2.79/1.00  --out_options                           all
% 2.79/1.00  --tptp_safe_out                         true
% 2.79/1.00  --problem_path                          ""
% 2.79/1.00  --include_path                          ""
% 2.79/1.00  --clausifier                            res/vclausify_rel
% 2.79/1.00  --clausifier_options                    --mode clausify
% 2.79/1.00  --stdin                                 false
% 2.79/1.00  --stats_out                             all
% 2.79/1.00  
% 2.79/1.00  ------ General Options
% 2.79/1.00  
% 2.79/1.00  --fof                                   false
% 2.79/1.00  --time_out_real                         305.
% 2.79/1.00  --time_out_virtual                      -1.
% 2.79/1.00  --symbol_type_check                     false
% 2.79/1.00  --clausify_out                          false
% 2.79/1.00  --sig_cnt_out                           false
% 2.79/1.00  --trig_cnt_out                          false
% 2.79/1.00  --trig_cnt_out_tolerance                1.
% 2.79/1.00  --trig_cnt_out_sk_spl                   false
% 2.79/1.00  --abstr_cl_out                          false
% 2.79/1.00  
% 2.79/1.00  ------ Global Options
% 2.79/1.00  
% 2.79/1.00  --schedule                              default
% 2.79/1.00  --add_important_lit                     false
% 2.79/1.00  --prop_solver_per_cl                    1000
% 2.79/1.00  --min_unsat_core                        false
% 2.79/1.00  --soft_assumptions                      false
% 2.79/1.00  --soft_lemma_size                       3
% 2.79/1.00  --prop_impl_unit_size                   0
% 2.79/1.00  --prop_impl_unit                        []
% 2.79/1.00  --share_sel_clauses                     true
% 2.79/1.00  --reset_solvers                         false
% 2.79/1.00  --bc_imp_inh                            [conj_cone]
% 2.79/1.00  --conj_cone_tolerance                   3.
% 2.79/1.00  --extra_neg_conj                        none
% 2.79/1.00  --large_theory_mode                     true
% 2.79/1.00  --prolific_symb_bound                   200
% 2.79/1.00  --lt_threshold                          2000
% 2.79/1.00  --clause_weak_htbl                      true
% 2.79/1.00  --gc_record_bc_elim                     false
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing Options
% 2.79/1.00  
% 2.79/1.00  --preprocessing_flag                    true
% 2.79/1.00  --time_out_prep_mult                    0.1
% 2.79/1.00  --splitting_mode                        input
% 2.79/1.00  --splitting_grd                         true
% 2.79/1.00  --splitting_cvd                         false
% 2.79/1.00  --splitting_cvd_svl                     false
% 2.79/1.00  --splitting_nvd                         32
% 2.79/1.00  --sub_typing                            true
% 2.79/1.00  --prep_gs_sim                           true
% 2.79/1.00  --prep_unflatten                        true
% 2.79/1.00  --prep_res_sim                          true
% 2.79/1.00  --prep_upred                            true
% 2.79/1.00  --prep_sem_filter                       exhaustive
% 2.79/1.00  --prep_sem_filter_out                   false
% 2.79/1.00  --pred_elim                             true
% 2.79/1.00  --res_sim_input                         true
% 2.79/1.00  --eq_ax_congr_red                       true
% 2.79/1.00  --pure_diseq_elim                       true
% 2.79/1.00  --brand_transform                       false
% 2.79/1.00  --non_eq_to_eq                          false
% 2.79/1.00  --prep_def_merge                        true
% 2.79/1.00  --prep_def_merge_prop_impl              false
% 2.79/1.00  --prep_def_merge_mbd                    true
% 2.79/1.00  --prep_def_merge_tr_red                 false
% 2.79/1.00  --prep_def_merge_tr_cl                  false
% 2.79/1.00  --smt_preprocessing                     true
% 2.79/1.00  --smt_ac_axioms                         fast
% 2.79/1.00  --preprocessed_out                      false
% 2.79/1.00  --preprocessed_stats                    false
% 2.79/1.00  
% 2.79/1.00  ------ Abstraction refinement Options
% 2.79/1.00  
% 2.79/1.00  --abstr_ref                             []
% 2.79/1.00  --abstr_ref_prep                        false
% 2.79/1.00  --abstr_ref_until_sat                   false
% 2.79/1.00  --abstr_ref_sig_restrict                funpre
% 2.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/1.00  --abstr_ref_under                       []
% 2.79/1.00  
% 2.79/1.00  ------ SAT Options
% 2.79/1.00  
% 2.79/1.00  --sat_mode                              false
% 2.79/1.00  --sat_fm_restart_options                ""
% 2.79/1.00  --sat_gr_def                            false
% 2.79/1.00  --sat_epr_types                         true
% 2.79/1.00  --sat_non_cyclic_types                  false
% 2.79/1.00  --sat_finite_models                     false
% 2.79/1.00  --sat_fm_lemmas                         false
% 2.79/1.00  --sat_fm_prep                           false
% 2.79/1.00  --sat_fm_uc_incr                        true
% 2.79/1.00  --sat_out_model                         small
% 2.79/1.00  --sat_out_clauses                       false
% 2.79/1.00  
% 2.79/1.00  ------ QBF Options
% 2.79/1.00  
% 2.79/1.00  --qbf_mode                              false
% 2.79/1.00  --qbf_elim_univ                         false
% 2.79/1.00  --qbf_dom_inst                          none
% 2.79/1.00  --qbf_dom_pre_inst                      false
% 2.79/1.00  --qbf_sk_in                             false
% 2.79/1.00  --qbf_pred_elim                         true
% 2.79/1.00  --qbf_split                             512
% 2.79/1.00  
% 2.79/1.00  ------ BMC1 Options
% 2.79/1.00  
% 2.79/1.00  --bmc1_incremental                      false
% 2.79/1.00  --bmc1_axioms                           reachable_all
% 2.79/1.00  --bmc1_min_bound                        0
% 2.79/1.00  --bmc1_max_bound                        -1
% 2.79/1.00  --bmc1_max_bound_default                -1
% 2.79/1.00  --bmc1_symbol_reachability              true
% 2.79/1.00  --bmc1_property_lemmas                  false
% 2.79/1.00  --bmc1_k_induction                      false
% 2.79/1.00  --bmc1_non_equiv_states                 false
% 2.79/1.00  --bmc1_deadlock                         false
% 2.79/1.00  --bmc1_ucm                              false
% 2.79/1.00  --bmc1_add_unsat_core                   none
% 2.79/1.00  --bmc1_unsat_core_children              false
% 2.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/1.00  --bmc1_out_stat                         full
% 2.79/1.00  --bmc1_ground_init                      false
% 2.79/1.00  --bmc1_pre_inst_next_state              false
% 2.79/1.00  --bmc1_pre_inst_state                   false
% 2.79/1.00  --bmc1_pre_inst_reach_state             false
% 2.79/1.00  --bmc1_out_unsat_core                   false
% 2.79/1.00  --bmc1_aig_witness_out                  false
% 2.79/1.00  --bmc1_verbose                          false
% 2.79/1.00  --bmc1_dump_clauses_tptp                false
% 2.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.79/1.00  --bmc1_dump_file                        -
% 2.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.79/1.00  --bmc1_ucm_extend_mode                  1
% 2.79/1.00  --bmc1_ucm_init_mode                    2
% 2.79/1.00  --bmc1_ucm_cone_mode                    none
% 2.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.79/1.00  --bmc1_ucm_relax_model                  4
% 2.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/1.00  --bmc1_ucm_layered_model                none
% 2.79/1.00  --bmc1_ucm_max_lemma_size               10
% 2.79/1.00  
% 2.79/1.00  ------ AIG Options
% 2.79/1.00  
% 2.79/1.00  --aig_mode                              false
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation Options
% 2.79/1.00  
% 2.79/1.00  --instantiation_flag                    true
% 2.79/1.00  --inst_sos_flag                         false
% 2.79/1.00  --inst_sos_phase                        true
% 2.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/1.00  --inst_lit_sel_side                     none
% 2.79/1.00  --inst_solver_per_active                1400
% 2.79/1.00  --inst_solver_calls_frac                1.
% 2.79/1.00  --inst_passive_queue_type               priority_queues
% 2.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/1.00  --inst_passive_queues_freq              [25;2]
% 2.79/1.00  --inst_dismatching                      true
% 2.79/1.00  --inst_eager_unprocessed_to_passive     true
% 2.79/1.00  --inst_prop_sim_given                   true
% 2.79/1.00  --inst_prop_sim_new                     false
% 2.79/1.00  --inst_subs_new                         false
% 2.79/1.00  --inst_eq_res_simp                      false
% 2.79/1.00  --inst_subs_given                       false
% 2.79/1.00  --inst_orphan_elimination               true
% 2.79/1.00  --inst_learning_loop_flag               true
% 2.79/1.00  --inst_learning_start                   3000
% 2.79/1.00  --inst_learning_factor                  2
% 2.79/1.00  --inst_start_prop_sim_after_learn       3
% 2.79/1.00  --inst_sel_renew                        solver
% 2.79/1.00  --inst_lit_activity_flag                true
% 2.79/1.00  --inst_restr_to_given                   false
% 2.79/1.00  --inst_activity_threshold               500
% 2.79/1.00  --inst_out_proof                        true
% 2.79/1.00  
% 2.79/1.00  ------ Resolution Options
% 2.79/1.00  
% 2.79/1.00  --resolution_flag                       false
% 2.79/1.00  --res_lit_sel                           adaptive
% 2.79/1.00  --res_lit_sel_side                      none
% 2.79/1.00  --res_ordering                          kbo
% 2.79/1.00  --res_to_prop_solver                    active
% 2.79/1.00  --res_prop_simpl_new                    false
% 2.79/1.00  --res_prop_simpl_given                  true
% 2.79/1.00  --res_passive_queue_type                priority_queues
% 2.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/1.00  --res_passive_queues_freq               [15;5]
% 2.79/1.00  --res_forward_subs                      full
% 2.79/1.00  --res_backward_subs                     full
% 2.79/1.00  --res_forward_subs_resolution           true
% 2.79/1.00  --res_backward_subs_resolution          true
% 2.79/1.00  --res_orphan_elimination                true
% 2.79/1.00  --res_time_limit                        2.
% 2.79/1.00  --res_out_proof                         true
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Options
% 2.79/1.00  
% 2.79/1.00  --superposition_flag                    true
% 2.79/1.00  --sup_passive_queue_type                priority_queues
% 2.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.79/1.00  --demod_completeness_check              fast
% 2.79/1.00  --demod_use_ground                      true
% 2.79/1.00  --sup_to_prop_solver                    passive
% 2.79/1.00  --sup_prop_simpl_new                    true
% 2.79/1.00  --sup_prop_simpl_given                  true
% 2.79/1.00  --sup_fun_splitting                     false
% 2.79/1.00  --sup_smt_interval                      50000
% 2.79/1.00  
% 2.79/1.00  ------ Superposition Simplification Setup
% 2.79/1.00  
% 2.79/1.00  --sup_indices_passive                   []
% 2.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_full_bw                           [BwDemod]
% 2.79/1.00  --sup_immed_triv                        [TrivRules]
% 2.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_immed_bw_main                     []
% 2.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.00  
% 2.79/1.00  ------ Combination Options
% 2.79/1.00  
% 2.79/1.00  --comb_res_mult                         3
% 2.79/1.00  --comb_sup_mult                         2
% 2.79/1.00  --comb_inst_mult                        10
% 2.79/1.00  
% 2.79/1.00  ------ Debug Options
% 2.79/1.00  
% 2.79/1.00  --dbg_backtrace                         false
% 2.79/1.00  --dbg_dump_prop_clauses                 false
% 2.79/1.00  --dbg_dump_prop_clauses_file            -
% 2.79/1.00  --dbg_out_stat                          false
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  ------ Proving...
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  % SZS status Theorem for theBenchmark.p
% 2.79/1.00  
% 2.79/1.00   Resolution empty clause
% 2.79/1.00  
% 2.79/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/1.00  
% 2.79/1.00  fof(f19,conjecture,(
% 2.79/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f20,negated_conjecture,(
% 2.79/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.79/1.00    inference(negated_conjecture,[],[f19])).
% 2.79/1.00  
% 2.79/1.00  fof(f35,plain,(
% 2.79/1.00    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.79/1.00    inference(ennf_transformation,[],[f20])).
% 2.79/1.00  
% 2.79/1.00  fof(f36,plain,(
% 2.79/1.00    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.79/1.00    inference(flattening,[],[f35])).
% 2.79/1.00  
% 2.79/1.00  fof(f49,plain,(
% 2.79/1.00    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK4),X0) & m1_subset_1(sK4,X0))) )),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f48,plain,(
% 2.79/1.00    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,X1),sK3) & m1_subset_1(X1,sK3)) & ~v1_xboole_0(sK3))),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f50,plain,(
% 2.79/1.00    (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,sK4),sK3) & m1_subset_1(sK4,sK3)) & ~v1_xboole_0(sK3)),
% 2.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f36,f49,f48])).
% 2.79/1.00  
% 2.79/1.00  fof(f84,plain,(
% 2.79/1.00    m1_subset_1(sK4,sK3)),
% 2.79/1.00    inference(cnf_transformation,[],[f50])).
% 2.79/1.00  
% 2.79/1.00  fof(f17,axiom,(
% 2.79/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f31,plain,(
% 2.79/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.79/1.00    inference(ennf_transformation,[],[f17])).
% 2.79/1.00  
% 2.79/1.00  fof(f32,plain,(
% 2.79/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.79/1.00    inference(flattening,[],[f31])).
% 2.79/1.00  
% 2.79/1.00  fof(f81,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f32])).
% 2.79/1.00  
% 2.79/1.00  fof(f3,axiom,(
% 2.79/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f53,plain,(
% 2.79/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f3])).
% 2.79/1.00  
% 2.79/1.00  fof(f4,axiom,(
% 2.79/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f54,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f4])).
% 2.79/1.00  
% 2.79/1.00  fof(f5,axiom,(
% 2.79/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f55,plain,(
% 2.79/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f5])).
% 2.79/1.00  
% 2.79/1.00  fof(f6,axiom,(
% 2.79/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f56,plain,(
% 2.79/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f6])).
% 2.79/1.00  
% 2.79/1.00  fof(f7,axiom,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f57,plain,(
% 2.79/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f7])).
% 2.79/1.00  
% 2.79/1.00  fof(f8,axiom,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f58,plain,(
% 2.79/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f8])).
% 2.79/1.00  
% 2.79/1.00  fof(f9,axiom,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f59,plain,(
% 2.79/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f9])).
% 2.79/1.00  
% 2.79/1.00  fof(f87,plain,(
% 2.79/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.79/1.00    inference(definition_unfolding,[],[f58,f59])).
% 2.79/1.00  
% 2.79/1.00  fof(f88,plain,(
% 2.79/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.79/1.00    inference(definition_unfolding,[],[f57,f87])).
% 2.79/1.00  
% 2.79/1.00  fof(f89,plain,(
% 2.79/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.79/1.00    inference(definition_unfolding,[],[f56,f88])).
% 2.79/1.00  
% 2.79/1.00  fof(f90,plain,(
% 2.79/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.79/1.00    inference(definition_unfolding,[],[f55,f89])).
% 2.79/1.00  
% 2.79/1.00  fof(f91,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.79/1.00    inference(definition_unfolding,[],[f54,f90])).
% 2.79/1.00  
% 2.79/1.00  fof(f92,plain,(
% 2.79/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.79/1.00    inference(definition_unfolding,[],[f53,f91])).
% 2.79/1.00  
% 2.79/1.00  fof(f93,plain,(
% 2.79/1.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.79/1.00    inference(definition_unfolding,[],[f81,f92])).
% 2.79/1.00  
% 2.79/1.00  fof(f1,axiom,(
% 2.79/1.00    v1_xboole_0(k1_xboole_0)),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f51,plain,(
% 2.79/1.00    v1_xboole_0(k1_xboole_0)),
% 2.79/1.00    inference(cnf_transformation,[],[f1])).
% 2.79/1.00  
% 2.79/1.00  fof(f85,plain,(
% 2.79/1.00    v1_subset_1(k6_domain_1(sK3,sK4),sK3)),
% 2.79/1.00    inference(cnf_transformation,[],[f50])).
% 2.79/1.00  
% 2.79/1.00  fof(f18,axiom,(
% 2.79/1.00    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f33,plain,(
% 2.79/1.00    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.79/1.00    inference(ennf_transformation,[],[f18])).
% 2.79/1.00  
% 2.79/1.00  fof(f34,plain,(
% 2.79/1.00    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.79/1.00    inference(flattening,[],[f33])).
% 2.79/1.00  
% 2.79/1.00  fof(f82,plain,(
% 2.79/1.00    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f34])).
% 2.79/1.00  
% 2.79/1.00  fof(f12,axiom,(
% 2.79/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f24,plain,(
% 2.79/1.00    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.79/1.00    inference(ennf_transformation,[],[f12])).
% 2.79/1.00  
% 2.79/1.00  fof(f76,plain,(
% 2.79/1.00    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f24])).
% 2.79/1.00  
% 2.79/1.00  fof(f86,plain,(
% 2.79/1.00    v1_zfmisc_1(sK3)),
% 2.79/1.00    inference(cnf_transformation,[],[f50])).
% 2.79/1.00  
% 2.79/1.00  fof(f83,plain,(
% 2.79/1.00    ~v1_xboole_0(sK3)),
% 2.79/1.00    inference(cnf_transformation,[],[f50])).
% 2.79/1.00  
% 2.79/1.00  fof(f16,axiom,(
% 2.79/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f29,plain,(
% 2.79/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.79/1.00    inference(ennf_transformation,[],[f16])).
% 2.79/1.00  
% 2.79/1.00  fof(f30,plain,(
% 2.79/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.79/1.00    inference(flattening,[],[f29])).
% 2.79/1.00  
% 2.79/1.00  fof(f80,plain,(
% 2.79/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f30])).
% 2.79/1.00  
% 2.79/1.00  fof(f2,axiom,(
% 2.79/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f22,plain,(
% 2.79/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.79/1.00    inference(ennf_transformation,[],[f2])).
% 2.79/1.00  
% 2.79/1.00  fof(f52,plain,(
% 2.79/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f22])).
% 2.79/1.00  
% 2.79/1.00  fof(f10,axiom,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f23,plain,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 2.79/1.00    inference(ennf_transformation,[],[f10])).
% 2.79/1.00  
% 2.79/1.00  fof(f38,plain,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.79/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.79/1.00  
% 2.79/1.00  fof(f37,plain,(
% 2.79/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.79/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.79/1.00  
% 2.79/1.00  fof(f39,plain,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 2.79/1.00    inference(definition_folding,[],[f23,f38,f37])).
% 2.79/1.00  
% 2.79/1.00  fof(f47,plain,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 2.79/1.00    inference(nnf_transformation,[],[f39])).
% 2.79/1.00  
% 2.79/1.00  fof(f73,plain,(
% 2.79/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 2.79/1.00    inference(cnf_transformation,[],[f47])).
% 2.79/1.00  
% 2.79/1.00  fof(f102,plain,(
% 2.79/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.79/1.00    inference(equality_resolution,[],[f73])).
% 2.79/1.00  
% 2.79/1.00  fof(f44,plain,(
% 2.79/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.79/1.00    inference(nnf_transformation,[],[f37])).
% 2.79/1.00  
% 2.79/1.00  fof(f45,plain,(
% 2.79/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.79/1.00    inference(flattening,[],[f44])).
% 2.79/1.00  
% 2.79/1.00  fof(f46,plain,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.79/1.00    inference(rectify,[],[f45])).
% 2.79/1.00  
% 2.79/1.00  fof(f72,plain,(
% 2.79/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 2.79/1.00    inference(cnf_transformation,[],[f46])).
% 2.79/1.00  
% 2.79/1.00  fof(f94,plain,(
% 2.79/1.00    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.79/1.00    inference(equality_resolution,[],[f72])).
% 2.79/1.00  
% 2.79/1.00  fof(f40,plain,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.79/1.00    inference(nnf_transformation,[],[f38])).
% 2.79/1.00  
% 2.79/1.00  fof(f41,plain,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.79/1.00    inference(rectify,[],[f40])).
% 2.79/1.00  
% 2.79/1.00  fof(f42,plain,(
% 2.79/1.00    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 2.79/1.00    introduced(choice_axiom,[])).
% 2.79/1.00  
% 2.79/1.00  fof(f43,plain,(
% 2.79/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 2.79/1.00  
% 2.79/1.00  fof(f61,plain,(
% 2.79/1.00    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f43])).
% 2.79/1.00  
% 2.79/1.00  fof(f11,axiom,(
% 2.79/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f75,plain,(
% 2.79/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f11])).
% 2.79/1.00  
% 2.79/1.00  fof(f13,axiom,(
% 2.79/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f21,plain,(
% 2.79/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.79/1.00    inference(unused_predicate_definition_removal,[],[f13])).
% 2.79/1.00  
% 2.79/1.00  fof(f25,plain,(
% 2.79/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.79/1.00    inference(ennf_transformation,[],[f21])).
% 2.79/1.00  
% 2.79/1.00  fof(f77,plain,(
% 2.79/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.79/1.00    inference(cnf_transformation,[],[f25])).
% 2.79/1.00  
% 2.79/1.00  fof(f15,axiom,(
% 2.79/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.79/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.00  
% 2.79/1.00  fof(f28,plain,(
% 2.79/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.79/1.00    inference(ennf_transformation,[],[f15])).
% 2.79/1.00  
% 2.79/1.00  fof(f79,plain,(
% 2.79/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.79/1.00    inference(cnf_transformation,[],[f28])).
% 2.79/1.00  
% 2.79/1.00  cnf(c_27,negated_conjecture,
% 2.79/1.00      ( m1_subset_1(sK4,sK3) ),
% 2.79/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2297,plain,
% 2.79/1.00      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_23,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,X1)
% 2.79/1.00      | v1_xboole_0(X1)
% 2.79/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2298,plain,
% 2.79/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
% 2.79/1.00      | m1_subset_1(X0,X1) != iProver_top
% 2.79/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3320,plain,
% 2.79/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(sK3,sK4)
% 2.79/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_2297,c_2298]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_0,plain,
% 2.79/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2318,plain,
% 2.79/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_26,negated_conjecture,
% 2.79/1.00      ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
% 2.79/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_24,plain,
% 2.79/1.00      ( ~ v1_subset_1(X0,X1)
% 2.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.79/1.00      | ~ v1_zfmisc_1(X1)
% 2.79/1.00      | v1_xboole_0(X0)
% 2.79/1.00      | v1_xboole_0(X1) ),
% 2.79/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_18,plain,
% 2.79/1.00      ( ~ v1_subset_1(X0,X1)
% 2.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.79/1.00      | ~ v1_xboole_0(X1) ),
% 2.79/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_149,plain,
% 2.79/1.00      ( v1_xboole_0(X0)
% 2.79/1.00      | ~ v1_zfmisc_1(X1)
% 2.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.79/1.00      | ~ v1_subset_1(X0,X1) ),
% 2.79/1.00      inference(global_propositional_subsumption,[status(thm)],[c_24,c_18]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_150,plain,
% 2.79/1.00      ( ~ v1_subset_1(X0,X1)
% 2.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.79/1.00      | ~ v1_zfmisc_1(X1)
% 2.79/1.00      | v1_xboole_0(X0) ),
% 2.79/1.00      inference(renaming,[status(thm)],[c_149]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_25,negated_conjecture,
% 2.79/1.00      ( v1_zfmisc_1(sK3) ),
% 2.79/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_321,plain,
% 2.79/1.00      ( ~ v1_subset_1(X0,X1)
% 2.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.79/1.00      | v1_xboole_0(X0)
% 2.79/1.00      | sK3 != X1 ),
% 2.79/1.00      inference(resolution_lifted,[status(thm)],[c_150,c_25]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_322,plain,
% 2.79/1.00      ( ~ v1_subset_1(X0,sK3)
% 2.79/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 2.79/1.00      | v1_xboole_0(X0) ),
% 2.79/1.00      inference(unflattening,[status(thm)],[c_321]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_342,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 2.79/1.00      | v1_xboole_0(X0)
% 2.79/1.00      | k6_domain_1(sK3,sK4) != X0
% 2.79/1.00      | sK3 != sK3 ),
% 2.79/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_322]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_343,plain,
% 2.79/1.00      ( ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
% 2.79/1.00      | v1_xboole_0(k6_domain_1(sK3,sK4)) ),
% 2.79/1.00      inference(unflattening,[status(thm)],[c_342]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2294,plain,
% 2.79/1.00      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
% 2.79/1.00      | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_28,negated_conjecture,
% 2.79/1.00      ( ~ v1_xboole_0(sK3) ),
% 2.79/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_29,plain,
% 2.79/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_30,plain,
% 2.79/1.00      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_344,plain,
% 2.79/1.00      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
% 2.79/1.00      | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_22,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,X1)
% 2.79/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.79/1.00      | v1_xboole_0(X1) ),
% 2.79/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2496,plain,
% 2.79/1.00      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
% 2.79/1.00      | ~ m1_subset_1(sK4,sK3)
% 2.79/1.00      | v1_xboole_0(sK3) ),
% 2.79/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2497,plain,
% 2.79/1.00      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
% 2.79/1.00      | m1_subset_1(sK4,sK3) != iProver_top
% 2.79/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2496]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2522,plain,
% 2.79/1.00      ( v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
% 2.79/1.00      inference(global_propositional_subsumption,
% 2.79/1.00                [status(thm)],
% 2.79/1.00                [c_2294,c_29,c_30,c_344,c_2497]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_1,plain,
% 2.79/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.79/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2317,plain,
% 2.79/1.00      ( X0 = X1
% 2.79/1.00      | v1_xboole_0(X1) != iProver_top
% 2.79/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2973,plain,
% 2.79/1.00      ( k6_domain_1(sK3,sK4) = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_2522,c_2317]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3069,plain,
% 2.79/1.00      ( k6_domain_1(sK3,sK4) = k1_xboole_0 ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_2318,c_2973]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3323,plain,
% 2.79/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 2.79/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.79/1.00      inference(light_normalisation,[status(thm)],[c_3320,c_3069]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3707,plain,
% 2.79/1.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 2.79/1.00      inference(global_propositional_subsumption,[status(thm)],[c_3323,c_29]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_16,plain,
% 2.79/1.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f102]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2302,plain,
% 2.79/1.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3710,plain,
% 2.79/1.00      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_3707,c_2302]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_6,plain,
% 2.79/1.00      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 2.79/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2312,plain,
% 2.79/1.00      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4,plain,
% 2.79/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.79/1.00      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 2.79/1.00      | r2_hidden(X0,X9) ),
% 2.79/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2314,plain,
% 2.79/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.79/1.00      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 2.79/1.00      | r2_hidden(X0,X9) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_3922,plain,
% 2.79/1.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.79/1.00      | r2_hidden(X7,X8) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_2312,c_2314]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4189,plain,
% 2.79/1.00      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_3710,c_3922]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_17,plain,
% 2.79/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2301,plain,
% 2.79/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_19,plain,
% 2.79/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.79/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_21,plain,
% 2.79/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.79/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_307,plain,
% 2.79/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r2_hidden(X1,X0) ),
% 2.79/1.00      inference(resolution,[status(thm)],[c_19,c_21]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2295,plain,
% 2.79/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.79/1.00      | r2_hidden(X1,X0) != iProver_top ),
% 2.79/1.00      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_2641,plain,
% 2.79/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.79/1.00      inference(superposition,[status(thm)],[c_2301,c_2295]) ).
% 2.79/1.00  
% 2.79/1.00  cnf(c_4200,plain,
% 2.79/1.00      ( $false ),
% 2.79/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4189,c_2641]) ).
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/1.00  
% 2.79/1.00  ------                               Statistics
% 2.79/1.00  
% 2.79/1.00  ------ General
% 2.79/1.00  
% 2.79/1.00  abstr_ref_over_cycles:                  0
% 2.79/1.00  abstr_ref_under_cycles:                 0
% 2.79/1.00  gc_basic_clause_elim:                   0
% 2.79/1.00  forced_gc_time:                         0
% 2.79/1.00  parsing_time:                           0.011
% 2.79/1.00  unif_index_cands_time:                  0.
% 2.79/1.00  unif_index_add_time:                    0.
% 2.79/1.00  orderings_time:                         0.
% 2.79/1.00  out_proof_time:                         0.011
% 2.79/1.00  total_time:                             0.177
% 2.79/1.00  num_of_symbols:                         46
% 2.79/1.00  num_of_terms:                           3440
% 2.79/1.00  
% 2.79/1.00  ------ Preprocessing
% 2.79/1.00  
% 2.79/1.00  num_of_splits:                          0
% 2.79/1.00  num_of_split_atoms:                     0
% 2.79/1.00  num_of_reused_defs:                     0
% 2.79/1.00  num_eq_ax_congr_red:                    105
% 2.79/1.00  num_of_sem_filtered_clauses:            1
% 2.79/1.00  num_of_subtypes:                        0
% 2.79/1.00  monotx_restored_types:                  0
% 2.79/1.00  sat_num_of_epr_types:                   0
% 2.79/1.00  sat_num_of_non_cyclic_types:            0
% 2.79/1.00  sat_guarded_non_collapsed_types:        0
% 2.79/1.00  num_pure_diseq_elim:                    0
% 2.79/1.00  simp_replaced_by:                       0
% 2.79/1.00  res_preprocessed:                       123
% 2.79/1.00  prep_upred:                             0
% 2.79/1.00  prep_unflattend:                        624
% 2.79/1.00  smt_new_axioms:                         0
% 2.79/1.00  pred_elim_cands:                        5
% 2.79/1.00  pred_elim:                              3
% 2.79/1.00  pred_elim_cl:                           4
% 2.79/1.00  pred_elim_cycles:                       9
% 2.79/1.00  merged_defs:                            0
% 2.79/1.00  merged_defs_ncl:                        0
% 2.79/1.00  bin_hyper_res:                          0
% 2.79/1.00  prep_cycles:                            4
% 2.79/1.00  pred_elim_time:                         0.043
% 2.79/1.00  splitting_time:                         0.
% 2.79/1.00  sem_filter_time:                        0.
% 2.79/1.00  monotx_time:                            0.001
% 2.79/1.00  subtype_inf_time:                       0.
% 2.79/1.00  
% 2.79/1.00  ------ Problem properties
% 2.79/1.00  
% 2.79/1.00  clauses:                                25
% 2.79/1.00  conjectures:                            2
% 2.79/1.00  epr:                                    15
% 2.79/1.00  horn:                                   21
% 2.79/1.00  ground:                                 4
% 2.79/1.00  unary:                                  13
% 2.79/1.00  binary:                                 3
% 2.79/1.00  lits:                                   52
% 2.79/1.00  lits_eq:                                11
% 2.79/1.00  fd_pure:                                0
% 2.79/1.00  fd_pseudo:                              0
% 2.79/1.00  fd_cond:                                0
% 2.79/1.00  fd_pseudo_cond:                         3
% 2.79/1.00  ac_symbols:                             0
% 2.79/1.00  
% 2.79/1.00  ------ Propositional Solver
% 2.79/1.00  
% 2.79/1.00  prop_solver_calls:                      28
% 2.79/1.00  prop_fast_solver_calls:                 852
% 2.79/1.00  smt_solver_calls:                       0
% 2.79/1.00  smt_fast_solver_calls:                  0
% 2.79/1.00  prop_num_of_clauses:                    961
% 2.79/1.00  prop_preprocess_simplified:             5667
% 2.79/1.00  prop_fo_subsumed:                       3
% 2.79/1.00  prop_solver_time:                       0.
% 2.79/1.00  smt_solver_time:                        0.
% 2.79/1.00  smt_fast_solver_time:                   0.
% 2.79/1.00  prop_fast_solver_time:                  0.
% 2.79/1.00  prop_unsat_core_time:                   0.
% 2.79/1.00  
% 2.79/1.00  ------ QBF
% 2.79/1.00  
% 2.79/1.00  qbf_q_res:                              0
% 2.79/1.00  qbf_num_tautologies:                    0
% 2.79/1.00  qbf_prep_cycles:                        0
% 2.79/1.00  
% 2.79/1.00  ------ BMC1
% 2.79/1.00  
% 2.79/1.00  bmc1_current_bound:                     -1
% 2.79/1.00  bmc1_last_solved_bound:                 -1
% 2.79/1.00  bmc1_unsat_core_size:                   -1
% 2.79/1.00  bmc1_unsat_core_parents_size:           -1
% 2.79/1.00  bmc1_merge_next_fun:                    0
% 2.79/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.79/1.00  
% 2.79/1.00  ------ Instantiation
% 2.79/1.00  
% 2.79/1.00  inst_num_of_clauses:                    300
% 2.79/1.00  inst_num_in_passive:                    146
% 2.79/1.00  inst_num_in_active:                     141
% 2.79/1.00  inst_num_in_unprocessed:                13
% 2.79/1.00  inst_num_of_loops:                      160
% 2.79/1.00  inst_num_of_learning_restarts:          0
% 2.79/1.00  inst_num_moves_active_passive:          16
% 2.79/1.00  inst_lit_activity:                      0
% 2.79/1.00  inst_lit_activity_moves:                0
% 2.79/1.00  inst_num_tautologies:                   0
% 2.79/1.00  inst_num_prop_implied:                  0
% 2.79/1.00  inst_num_existing_simplified:           0
% 2.79/1.00  inst_num_eq_res_simplified:             0
% 2.79/1.00  inst_num_child_elim:                    0
% 2.79/1.00  inst_num_of_dismatching_blockings:      104
% 2.79/1.00  inst_num_of_non_proper_insts:           293
% 2.79/1.00  inst_num_of_duplicates:                 0
% 2.79/1.00  inst_inst_num_from_inst_to_res:         0
% 2.79/1.00  inst_dismatching_checking_time:         0.
% 2.79/1.00  
% 2.79/1.00  ------ Resolution
% 2.79/1.00  
% 2.79/1.00  res_num_of_clauses:                     0
% 2.79/1.00  res_num_in_passive:                     0
% 2.79/1.00  res_num_in_active:                      0
% 2.79/1.00  res_num_of_loops:                       127
% 2.79/1.00  res_forward_subset_subsumed:            98
% 2.79/1.00  res_backward_subset_subsumed:           0
% 2.79/1.00  res_forward_subsumed:                   0
% 2.79/1.00  res_backward_subsumed:                  0
% 2.79/1.00  res_forward_subsumption_resolution:     0
% 2.79/1.00  res_backward_subsumption_resolution:    0
% 2.79/1.00  res_clause_to_clause_subsumption:       1155
% 2.79/1.00  res_orphan_elimination:                 0
% 2.79/1.00  res_tautology_del:                      44
% 2.79/1.00  res_num_eq_res_simplified:              0
% 2.79/1.00  res_num_sel_changes:                    0
% 2.79/1.00  res_moves_from_active_to_pass:          0
% 2.79/1.00  
% 2.79/1.00  ------ Superposition
% 2.79/1.00  
% 2.79/1.00  sup_time_total:                         0.
% 2.79/1.00  sup_time_generating:                    0.
% 2.79/1.00  sup_time_sim_full:                      0.
% 2.79/1.00  sup_time_sim_immed:                     0.
% 2.79/1.00  
% 2.79/1.00  sup_num_of_clauses:                     46
% 2.79/1.00  sup_num_in_active:                      29
% 2.79/1.00  sup_num_in_passive:                     17
% 2.79/1.00  sup_num_of_loops:                       31
% 2.79/1.00  sup_fw_superposition:                   24
% 2.79/1.00  sup_bw_superposition:                   6
% 2.79/1.00  sup_immediate_simplified:               5
% 2.79/1.00  sup_given_eliminated:                   1
% 2.79/1.00  comparisons_done:                       0
% 2.79/1.00  comparisons_avoided:                    0
% 2.79/1.00  
% 2.79/1.00  ------ Simplifications
% 2.79/1.00  
% 2.79/1.00  
% 2.79/1.00  sim_fw_subset_subsumed:                 2
% 2.79/1.00  sim_bw_subset_subsumed:                 0
% 2.79/1.00  sim_fw_subsumed:                        2
% 2.79/1.00  sim_bw_subsumed:                        0
% 2.79/1.00  sim_fw_subsumption_res:                 1
% 2.79/1.00  sim_bw_subsumption_res:                 0
% 2.79/1.00  sim_tautology_del:                      0
% 2.79/1.00  sim_eq_tautology_del:                   4
% 2.79/1.00  sim_eq_res_simp:                        0
% 2.79/1.00  sim_fw_demodulated:                     0
% 2.79/1.00  sim_bw_demodulated:                     2
% 2.79/1.00  sim_light_normalised:                   1
% 2.79/1.00  sim_joinable_taut:                      0
% 2.79/1.00  sim_joinable_simp:                      0
% 2.79/1.00  sim_ac_normalised:                      0
% 2.79/1.00  sim_smt_subsumption:                    0
% 2.79/1.00  
%------------------------------------------------------------------------------
