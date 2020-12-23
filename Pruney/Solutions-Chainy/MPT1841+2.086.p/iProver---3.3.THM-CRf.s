%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:06 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 242 expanded)
%              Number of clauses        :   51 (  66 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  389 ( 794 expanded)
%              Number of equality atoms :  175 ( 212 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK4),X0)
        & m1_subset_1(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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

fof(f45,plain,
    ( v1_zfmisc_1(sK3)
    & v1_subset_1(k6_domain_1(sK3,sK4),sK3)
    & m1_subset_1(sK4,sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f44,f43])).

fof(f80,plain,(
    v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f82])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f83])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f84])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f85])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f86])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f76,f87])).

fof(f12,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f30,plain,(
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

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f20,f31,f30])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f72])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f71])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2143,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2125,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_140,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_21])).

cnf(c_141,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_140])).

cnf(c_25,negated_conjecture,
    ( v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_141,c_25])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | ~ v1_subset_1(X0,sK3)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | v1_xboole_0(X0)
    | k6_domain_1(sK3,sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_283])).

cnf(c_302,plain,
    ( ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
    | v1_xboole_0(k6_domain_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_2121,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_3212,plain,
    ( m1_subset_1(sK4,sK3) != iProver_top
    | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2125,c_2121])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_303,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_2304,plain,
    ( ~ m1_subset_1(X0,sK3)
    | m1_subset_1(k6_domain_1(sK3,X0),k1_zfmisc_1(sK3))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2348,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_2349,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2348])).

cnf(c_4055,plain,
    ( v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3212,c_29,c_30,c_303,c_2349])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2142,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4060,plain,
    ( k6_domain_1(sK3,sK4) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4055,c_2142])).

cnf(c_4067,plain,
    ( k6_domain_1(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2143,c_4060])).

cnf(c_2123,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2124,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2434,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(sK3,sK4)
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_2124])).

cnf(c_2314,plain,
    ( ~ m1_subset_1(X0,sK3)
    | v1_xboole_0(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2394,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2314])).

cnf(c_2676,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2434,c_28,c_27,c_2394])).

cnf(c_20,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2126,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3231,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_domain_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_2126])).

cnf(c_4375,plain,
    ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4067,c_3231])).

cnf(c_10,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2136,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2138,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3854,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_2138])).

cnf(c_7590,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4375,c_3854])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2141,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2383,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_2141])).

cnf(c_8416,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7590,c_2383])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:12:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.91/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/0.99  
% 2.91/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.91/0.99  
% 2.91/0.99  ------  iProver source info
% 2.91/0.99  
% 2.91/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.91/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.91/0.99  git: non_committed_changes: false
% 2.91/0.99  git: last_make_outside_of_git: false
% 2.91/0.99  
% 2.91/0.99  ------ 
% 2.91/0.99  
% 2.91/0.99  ------ Input Options
% 2.91/0.99  
% 2.91/0.99  --out_options                           all
% 2.91/0.99  --tptp_safe_out                         true
% 2.91/0.99  --problem_path                          ""
% 2.91/0.99  --include_path                          ""
% 2.91/0.99  --clausifier                            res/vclausify_rel
% 2.91/0.99  --clausifier_options                    --mode clausify
% 2.91/0.99  --stdin                                 false
% 2.91/0.99  --stats_out                             all
% 2.91/0.99  
% 2.91/0.99  ------ General Options
% 2.91/0.99  
% 2.91/0.99  --fof                                   false
% 2.91/0.99  --time_out_real                         305.
% 2.91/0.99  --time_out_virtual                      -1.
% 2.91/0.99  --symbol_type_check                     false
% 2.91/0.99  --clausify_out                          false
% 2.91/0.99  --sig_cnt_out                           false
% 2.91/0.99  --trig_cnt_out                          false
% 2.91/0.99  --trig_cnt_out_tolerance                1.
% 2.91/0.99  --trig_cnt_out_sk_spl                   false
% 2.91/0.99  --abstr_cl_out                          false
% 2.91/0.99  
% 2.91/0.99  ------ Global Options
% 2.91/0.99  
% 2.91/0.99  --schedule                              default
% 2.91/0.99  --add_important_lit                     false
% 2.91/0.99  --prop_solver_per_cl                    1000
% 2.91/0.99  --min_unsat_core                        false
% 2.91/0.99  --soft_assumptions                      false
% 2.91/0.99  --soft_lemma_size                       3
% 2.91/0.99  --prop_impl_unit_size                   0
% 2.91/0.99  --prop_impl_unit                        []
% 2.91/0.99  --share_sel_clauses                     true
% 2.91/0.99  --reset_solvers                         false
% 2.91/0.99  --bc_imp_inh                            [conj_cone]
% 2.91/0.99  --conj_cone_tolerance                   3.
% 2.91/0.99  --extra_neg_conj                        none
% 2.91/0.99  --large_theory_mode                     true
% 2.91/0.99  --prolific_symb_bound                   200
% 2.91/0.99  --lt_threshold                          2000
% 2.91/0.99  --clause_weak_htbl                      true
% 2.91/0.99  --gc_record_bc_elim                     false
% 2.91/0.99  
% 2.91/0.99  ------ Preprocessing Options
% 2.91/0.99  
% 2.91/0.99  --preprocessing_flag                    true
% 2.91/0.99  --time_out_prep_mult                    0.1
% 2.91/0.99  --splitting_mode                        input
% 2.91/0.99  --splitting_grd                         true
% 2.91/0.99  --splitting_cvd                         false
% 2.91/0.99  --splitting_cvd_svl                     false
% 2.91/0.99  --splitting_nvd                         32
% 2.91/0.99  --sub_typing                            true
% 2.91/0.99  --prep_gs_sim                           true
% 2.91/0.99  --prep_unflatten                        true
% 2.91/0.99  --prep_res_sim                          true
% 2.91/0.99  --prep_upred                            true
% 2.91/0.99  --prep_sem_filter                       exhaustive
% 2.91/0.99  --prep_sem_filter_out                   false
% 2.91/0.99  --pred_elim                             true
% 2.91/0.99  --res_sim_input                         true
% 2.91/0.99  --eq_ax_congr_red                       true
% 2.91/0.99  --pure_diseq_elim                       true
% 2.91/0.99  --brand_transform                       false
% 2.91/0.99  --non_eq_to_eq                          false
% 2.91/0.99  --prep_def_merge                        true
% 2.91/0.99  --prep_def_merge_prop_impl              false
% 2.91/0.99  --prep_def_merge_mbd                    true
% 2.91/0.99  --prep_def_merge_tr_red                 false
% 2.91/0.99  --prep_def_merge_tr_cl                  false
% 2.91/0.99  --smt_preprocessing                     true
% 2.91/0.99  --smt_ac_axioms                         fast
% 2.91/0.99  --preprocessed_out                      false
% 2.91/0.99  --preprocessed_stats                    false
% 2.91/0.99  
% 2.91/0.99  ------ Abstraction refinement Options
% 2.91/0.99  
% 2.91/0.99  --abstr_ref                             []
% 2.91/0.99  --abstr_ref_prep                        false
% 2.91/0.99  --abstr_ref_until_sat                   false
% 2.91/0.99  --abstr_ref_sig_restrict                funpre
% 2.91/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/0.99  --abstr_ref_under                       []
% 2.91/0.99  
% 2.91/0.99  ------ SAT Options
% 2.91/0.99  
% 2.91/0.99  --sat_mode                              false
% 2.91/0.99  --sat_fm_restart_options                ""
% 2.91/0.99  --sat_gr_def                            false
% 2.91/0.99  --sat_epr_types                         true
% 2.91/0.99  --sat_non_cyclic_types                  false
% 2.91/0.99  --sat_finite_models                     false
% 2.91/0.99  --sat_fm_lemmas                         false
% 2.91/0.99  --sat_fm_prep                           false
% 2.91/0.99  --sat_fm_uc_incr                        true
% 2.91/0.99  --sat_out_model                         small
% 2.91/0.99  --sat_out_clauses                       false
% 2.91/0.99  
% 2.91/0.99  ------ QBF Options
% 2.91/0.99  
% 2.91/0.99  --qbf_mode                              false
% 2.91/0.99  --qbf_elim_univ                         false
% 2.91/0.99  --qbf_dom_inst                          none
% 2.91/0.99  --qbf_dom_pre_inst                      false
% 2.91/0.99  --qbf_sk_in                             false
% 2.91/0.99  --qbf_pred_elim                         true
% 2.91/0.99  --qbf_split                             512
% 2.91/0.99  
% 2.91/0.99  ------ BMC1 Options
% 2.91/0.99  
% 2.91/0.99  --bmc1_incremental                      false
% 2.91/0.99  --bmc1_axioms                           reachable_all
% 2.91/0.99  --bmc1_min_bound                        0
% 2.91/0.99  --bmc1_max_bound                        -1
% 2.91/0.99  --bmc1_max_bound_default                -1
% 2.91/0.99  --bmc1_symbol_reachability              true
% 2.91/0.99  --bmc1_property_lemmas                  false
% 2.91/0.99  --bmc1_k_induction                      false
% 2.91/0.99  --bmc1_non_equiv_states                 false
% 2.91/0.99  --bmc1_deadlock                         false
% 2.91/0.99  --bmc1_ucm                              false
% 2.91/0.99  --bmc1_add_unsat_core                   none
% 2.91/0.99  --bmc1_unsat_core_children              false
% 2.91/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/0.99  --bmc1_out_stat                         full
% 2.91/0.99  --bmc1_ground_init                      false
% 2.91/0.99  --bmc1_pre_inst_next_state              false
% 2.91/0.99  --bmc1_pre_inst_state                   false
% 2.91/0.99  --bmc1_pre_inst_reach_state             false
% 2.91/0.99  --bmc1_out_unsat_core                   false
% 2.91/0.99  --bmc1_aig_witness_out                  false
% 2.91/0.99  --bmc1_verbose                          false
% 2.91/0.99  --bmc1_dump_clauses_tptp                false
% 2.91/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.91/0.99  --bmc1_dump_file                        -
% 2.91/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.91/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.91/0.99  --bmc1_ucm_extend_mode                  1
% 2.91/0.99  --bmc1_ucm_init_mode                    2
% 2.91/0.99  --bmc1_ucm_cone_mode                    none
% 2.91/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.91/0.99  --bmc1_ucm_relax_model                  4
% 2.91/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.91/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/0.99  --bmc1_ucm_layered_model                none
% 2.91/0.99  --bmc1_ucm_max_lemma_size               10
% 2.91/0.99  
% 2.91/0.99  ------ AIG Options
% 2.91/0.99  
% 2.91/0.99  --aig_mode                              false
% 2.91/0.99  
% 2.91/0.99  ------ Instantiation Options
% 2.91/0.99  
% 2.91/0.99  --instantiation_flag                    true
% 2.91/0.99  --inst_sos_flag                         false
% 2.91/0.99  --inst_sos_phase                        true
% 2.91/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/0.99  --inst_lit_sel_side                     num_symb
% 2.91/0.99  --inst_solver_per_active                1400
% 2.91/0.99  --inst_solver_calls_frac                1.
% 2.91/0.99  --inst_passive_queue_type               priority_queues
% 2.91/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/0.99  --inst_passive_queues_freq              [25;2]
% 2.91/0.99  --inst_dismatching                      true
% 2.91/0.99  --inst_eager_unprocessed_to_passive     true
% 2.91/0.99  --inst_prop_sim_given                   true
% 2.91/0.99  --inst_prop_sim_new                     false
% 2.91/0.99  --inst_subs_new                         false
% 2.91/0.99  --inst_eq_res_simp                      false
% 2.91/0.99  --inst_subs_given                       false
% 2.91/0.99  --inst_orphan_elimination               true
% 2.91/0.99  --inst_learning_loop_flag               true
% 2.91/0.99  --inst_learning_start                   3000
% 2.91/0.99  --inst_learning_factor                  2
% 2.91/0.99  --inst_start_prop_sim_after_learn       3
% 2.91/0.99  --inst_sel_renew                        solver
% 2.91/0.99  --inst_lit_activity_flag                true
% 2.91/0.99  --inst_restr_to_given                   false
% 2.91/0.99  --inst_activity_threshold               500
% 2.91/0.99  --inst_out_proof                        true
% 2.91/0.99  
% 2.91/0.99  ------ Resolution Options
% 2.91/0.99  
% 2.91/0.99  --resolution_flag                       true
% 2.91/0.99  --res_lit_sel                           adaptive
% 2.91/0.99  --res_lit_sel_side                      none
% 2.91/0.99  --res_ordering                          kbo
% 2.91/0.99  --res_to_prop_solver                    active
% 2.91/0.99  --res_prop_simpl_new                    false
% 2.91/0.99  --res_prop_simpl_given                  true
% 2.91/0.99  --res_passive_queue_type                priority_queues
% 2.91/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/0.99  --res_passive_queues_freq               [15;5]
% 2.91/0.99  --res_forward_subs                      full
% 2.91/0.99  --res_backward_subs                     full
% 2.91/0.99  --res_forward_subs_resolution           true
% 2.91/0.99  --res_backward_subs_resolution          true
% 2.91/0.99  --res_orphan_elimination                true
% 2.91/0.99  --res_time_limit                        2.
% 2.91/0.99  --res_out_proof                         true
% 2.91/0.99  
% 2.91/0.99  ------ Superposition Options
% 2.91/0.99  
% 2.91/0.99  --superposition_flag                    true
% 2.91/0.99  --sup_passive_queue_type                priority_queues
% 2.91/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.91/0.99  --demod_completeness_check              fast
% 2.91/0.99  --demod_use_ground                      true
% 2.91/0.99  --sup_to_prop_solver                    passive
% 2.91/0.99  --sup_prop_simpl_new                    true
% 2.91/0.99  --sup_prop_simpl_given                  true
% 2.91/0.99  --sup_fun_splitting                     false
% 2.91/0.99  --sup_smt_interval                      50000
% 2.91/0.99  
% 2.91/0.99  ------ Superposition Simplification Setup
% 2.91/0.99  
% 2.91/0.99  --sup_indices_passive                   []
% 2.91/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.99  --sup_full_bw                           [BwDemod]
% 2.91/0.99  --sup_immed_triv                        [TrivRules]
% 2.91/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.99  --sup_immed_bw_main                     []
% 2.91/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/0.99  
% 2.91/0.99  ------ Combination Options
% 2.91/0.99  
% 2.91/0.99  --comb_res_mult                         3
% 2.91/0.99  --comb_sup_mult                         2
% 2.91/0.99  --comb_inst_mult                        10
% 2.91/0.99  
% 2.91/0.99  ------ Debug Options
% 2.91/0.99  
% 2.91/0.99  --dbg_backtrace                         false
% 2.91/0.99  --dbg_dump_prop_clauses                 false
% 2.91/0.99  --dbg_dump_prop_clauses_file            -
% 2.91/0.99  --dbg_out_stat                          false
% 2.91/0.99  ------ Parsing...
% 2.91/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.91/0.99  
% 2.91/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.91/0.99  
% 2.91/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.91/0.99  
% 2.91/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.91/0.99  ------ Proving...
% 2.91/0.99  ------ Problem Properties 
% 2.91/0.99  
% 2.91/0.99  
% 2.91/0.99  clauses                                 26
% 2.91/0.99  conjectures                             2
% 2.91/0.99  EPR                                     15
% 2.91/0.99  Horn                                    21
% 2.91/0.99  unary                                   15
% 2.91/0.99  binary                                  2
% 2.91/0.99  lits                                    52
% 2.91/0.99  lits eq                                 16
% 2.91/0.99  fd_pure                                 0
% 2.91/0.99  fd_pseudo                               0
% 2.91/0.99  fd_cond                                 1
% 2.91/0.99  fd_pseudo_cond                          3
% 2.91/0.99  AC symbols                              0
% 2.91/0.99  
% 2.91/0.99  ------ Schedule dynamic 5 is on 
% 2.91/0.99  
% 2.91/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.91/0.99  
% 2.91/0.99  
% 2.91/0.99  ------ 
% 2.91/0.99  Current options:
% 2.91/0.99  ------ 
% 2.91/0.99  
% 2.91/0.99  ------ Input Options
% 2.91/0.99  
% 2.91/0.99  --out_options                           all
% 2.91/0.99  --tptp_safe_out                         true
% 2.91/0.99  --problem_path                          ""
% 2.91/0.99  --include_path                          ""
% 2.91/0.99  --clausifier                            res/vclausify_rel
% 2.91/0.99  --clausifier_options                    --mode clausify
% 2.91/0.99  --stdin                                 false
% 2.91/0.99  --stats_out                             all
% 2.91/0.99  
% 2.91/0.99  ------ General Options
% 2.91/0.99  
% 2.91/0.99  --fof                                   false
% 2.91/0.99  --time_out_real                         305.
% 2.91/0.99  --time_out_virtual                      -1.
% 2.91/0.99  --symbol_type_check                     false
% 2.91/0.99  --clausify_out                          false
% 2.91/0.99  --sig_cnt_out                           false
% 2.91/0.99  --trig_cnt_out                          false
% 2.91/0.99  --trig_cnt_out_tolerance                1.
% 2.91/0.99  --trig_cnt_out_sk_spl                   false
% 2.91/0.99  --abstr_cl_out                          false
% 2.91/0.99  
% 2.91/0.99  ------ Global Options
% 2.91/0.99  
% 2.91/0.99  --schedule                              default
% 2.91/0.99  --add_important_lit                     false
% 2.91/0.99  --prop_solver_per_cl                    1000
% 2.91/0.99  --min_unsat_core                        false
% 2.91/0.99  --soft_assumptions                      false
% 2.91/0.99  --soft_lemma_size                       3
% 2.91/0.99  --prop_impl_unit_size                   0
% 2.91/0.99  --prop_impl_unit                        []
% 2.91/0.99  --share_sel_clauses                     true
% 2.91/0.99  --reset_solvers                         false
% 2.91/0.99  --bc_imp_inh                            [conj_cone]
% 2.91/0.99  --conj_cone_tolerance                   3.
% 2.91/0.99  --extra_neg_conj                        none
% 2.91/0.99  --large_theory_mode                     true
% 2.91/0.99  --prolific_symb_bound                   200
% 2.91/0.99  --lt_threshold                          2000
% 2.91/0.99  --clause_weak_htbl                      true
% 2.91/0.99  --gc_record_bc_elim                     false
% 2.91/0.99  
% 2.91/0.99  ------ Preprocessing Options
% 2.91/0.99  
% 2.91/0.99  --preprocessing_flag                    true
% 2.91/0.99  --time_out_prep_mult                    0.1
% 2.91/0.99  --splitting_mode                        input
% 2.91/0.99  --splitting_grd                         true
% 2.91/0.99  --splitting_cvd                         false
% 2.91/0.99  --splitting_cvd_svl                     false
% 2.91/0.99  --splitting_nvd                         32
% 2.91/0.99  --sub_typing                            true
% 2.91/0.99  --prep_gs_sim                           true
% 2.91/0.99  --prep_unflatten                        true
% 2.91/0.99  --prep_res_sim                          true
% 2.91/0.99  --prep_upred                            true
% 2.91/0.99  --prep_sem_filter                       exhaustive
% 2.91/0.99  --prep_sem_filter_out                   false
% 2.91/0.99  --pred_elim                             true
% 2.91/0.99  --res_sim_input                         true
% 2.91/0.99  --eq_ax_congr_red                       true
% 2.91/0.99  --pure_diseq_elim                       true
% 2.91/0.99  --brand_transform                       false
% 2.91/0.99  --non_eq_to_eq                          false
% 2.91/0.99  --prep_def_merge                        true
% 2.91/0.99  --prep_def_merge_prop_impl              false
% 2.91/0.99  --prep_def_merge_mbd                    true
% 2.91/0.99  --prep_def_merge_tr_red                 false
% 2.91/0.99  --prep_def_merge_tr_cl                  false
% 2.91/0.99  --smt_preprocessing                     true
% 2.91/0.99  --smt_ac_axioms                         fast
% 2.91/0.99  --preprocessed_out                      false
% 2.91/0.99  --preprocessed_stats                    false
% 2.91/0.99  
% 2.91/0.99  ------ Abstraction refinement Options
% 2.91/0.99  
% 2.91/0.99  --abstr_ref                             []
% 2.91/0.99  --abstr_ref_prep                        false
% 2.91/0.99  --abstr_ref_until_sat                   false
% 2.91/0.99  --abstr_ref_sig_restrict                funpre
% 2.91/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.91/0.99  --abstr_ref_under                       []
% 2.91/0.99  
% 2.91/0.99  ------ SAT Options
% 2.91/0.99  
% 2.91/0.99  --sat_mode                              false
% 2.91/0.99  --sat_fm_restart_options                ""
% 2.91/0.99  --sat_gr_def                            false
% 2.91/0.99  --sat_epr_types                         true
% 2.91/0.99  --sat_non_cyclic_types                  false
% 2.91/0.99  --sat_finite_models                     false
% 2.91/0.99  --sat_fm_lemmas                         false
% 2.91/0.99  --sat_fm_prep                           false
% 2.91/0.99  --sat_fm_uc_incr                        true
% 2.91/0.99  --sat_out_model                         small
% 2.91/0.99  --sat_out_clauses                       false
% 2.91/0.99  
% 2.91/0.99  ------ QBF Options
% 2.91/0.99  
% 2.91/0.99  --qbf_mode                              false
% 2.91/0.99  --qbf_elim_univ                         false
% 2.91/0.99  --qbf_dom_inst                          none
% 2.91/0.99  --qbf_dom_pre_inst                      false
% 2.91/0.99  --qbf_sk_in                             false
% 2.91/0.99  --qbf_pred_elim                         true
% 2.91/0.99  --qbf_split                             512
% 2.91/0.99  
% 2.91/0.99  ------ BMC1 Options
% 2.91/0.99  
% 2.91/0.99  --bmc1_incremental                      false
% 2.91/0.99  --bmc1_axioms                           reachable_all
% 2.91/0.99  --bmc1_min_bound                        0
% 2.91/0.99  --bmc1_max_bound                        -1
% 2.91/0.99  --bmc1_max_bound_default                -1
% 2.91/0.99  --bmc1_symbol_reachability              true
% 2.91/0.99  --bmc1_property_lemmas                  false
% 2.91/0.99  --bmc1_k_induction                      false
% 2.91/0.99  --bmc1_non_equiv_states                 false
% 2.91/0.99  --bmc1_deadlock                         false
% 2.91/0.99  --bmc1_ucm                              false
% 2.91/0.99  --bmc1_add_unsat_core                   none
% 2.91/0.99  --bmc1_unsat_core_children              false
% 2.91/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.91/0.99  --bmc1_out_stat                         full
% 2.91/0.99  --bmc1_ground_init                      false
% 2.91/0.99  --bmc1_pre_inst_next_state              false
% 2.91/0.99  --bmc1_pre_inst_state                   false
% 2.91/0.99  --bmc1_pre_inst_reach_state             false
% 2.91/0.99  --bmc1_out_unsat_core                   false
% 2.91/0.99  --bmc1_aig_witness_out                  false
% 2.91/0.99  --bmc1_verbose                          false
% 2.91/0.99  --bmc1_dump_clauses_tptp                false
% 2.91/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.91/0.99  --bmc1_dump_file                        -
% 2.91/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.91/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.91/0.99  --bmc1_ucm_extend_mode                  1
% 2.91/0.99  --bmc1_ucm_init_mode                    2
% 2.91/0.99  --bmc1_ucm_cone_mode                    none
% 2.91/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.91/0.99  --bmc1_ucm_relax_model                  4
% 2.91/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.91/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.91/0.99  --bmc1_ucm_layered_model                none
% 2.91/0.99  --bmc1_ucm_max_lemma_size               10
% 2.91/0.99  
% 2.91/0.99  ------ AIG Options
% 2.91/0.99  
% 2.91/0.99  --aig_mode                              false
% 2.91/0.99  
% 2.91/0.99  ------ Instantiation Options
% 2.91/0.99  
% 2.91/0.99  --instantiation_flag                    true
% 2.91/0.99  --inst_sos_flag                         false
% 2.91/0.99  --inst_sos_phase                        true
% 2.91/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.91/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.91/0.99  --inst_lit_sel_side                     none
% 2.91/0.99  --inst_solver_per_active                1400
% 2.91/0.99  --inst_solver_calls_frac                1.
% 2.91/0.99  --inst_passive_queue_type               priority_queues
% 2.91/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.91/0.99  --inst_passive_queues_freq              [25;2]
% 2.91/0.99  --inst_dismatching                      true
% 2.91/0.99  --inst_eager_unprocessed_to_passive     true
% 2.91/0.99  --inst_prop_sim_given                   true
% 2.91/0.99  --inst_prop_sim_new                     false
% 2.91/0.99  --inst_subs_new                         false
% 2.91/0.99  --inst_eq_res_simp                      false
% 2.91/0.99  --inst_subs_given                       false
% 2.91/0.99  --inst_orphan_elimination               true
% 2.91/0.99  --inst_learning_loop_flag               true
% 2.91/0.99  --inst_learning_start                   3000
% 2.91/0.99  --inst_learning_factor                  2
% 2.91/0.99  --inst_start_prop_sim_after_learn       3
% 2.91/0.99  --inst_sel_renew                        solver
% 2.91/0.99  --inst_lit_activity_flag                true
% 2.91/0.99  --inst_restr_to_given                   false
% 2.91/0.99  --inst_activity_threshold               500
% 2.91/0.99  --inst_out_proof                        true
% 2.91/0.99  
% 2.91/0.99  ------ Resolution Options
% 2.91/0.99  
% 2.91/0.99  --resolution_flag                       false
% 2.91/0.99  --res_lit_sel                           adaptive
% 2.91/0.99  --res_lit_sel_side                      none
% 2.91/0.99  --res_ordering                          kbo
% 2.91/0.99  --res_to_prop_solver                    active
% 2.91/0.99  --res_prop_simpl_new                    false
% 2.91/0.99  --res_prop_simpl_given                  true
% 2.91/0.99  --res_passive_queue_type                priority_queues
% 2.91/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.91/0.99  --res_passive_queues_freq               [15;5]
% 2.91/0.99  --res_forward_subs                      full
% 2.91/0.99  --res_backward_subs                     full
% 2.91/0.99  --res_forward_subs_resolution           true
% 2.91/0.99  --res_backward_subs_resolution          true
% 2.91/0.99  --res_orphan_elimination                true
% 2.91/0.99  --res_time_limit                        2.
% 2.91/0.99  --res_out_proof                         true
% 2.91/0.99  
% 2.91/0.99  ------ Superposition Options
% 2.91/0.99  
% 2.91/0.99  --superposition_flag                    true
% 2.91/0.99  --sup_passive_queue_type                priority_queues
% 2.91/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.91/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.91/0.99  --demod_completeness_check              fast
% 2.91/0.99  --demod_use_ground                      true
% 2.91/0.99  --sup_to_prop_solver                    passive
% 2.91/0.99  --sup_prop_simpl_new                    true
% 2.91/0.99  --sup_prop_simpl_given                  true
% 2.91/0.99  --sup_fun_splitting                     false
% 2.91/0.99  --sup_smt_interval                      50000
% 2.91/0.99  
% 2.91/0.99  ------ Superposition Simplification Setup
% 2.91/0.99  
% 2.91/0.99  --sup_indices_passive                   []
% 2.91/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.91/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.91/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.99  --sup_full_bw                           [BwDemod]
% 2.91/0.99  --sup_immed_triv                        [TrivRules]
% 2.91/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.91/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.99  --sup_immed_bw_main                     []
% 2.91/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.91/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.91/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.91/0.99  
% 2.91/0.99  ------ Combination Options
% 2.91/0.99  
% 2.91/0.99  --comb_res_mult                         3
% 2.91/0.99  --comb_sup_mult                         2
% 2.91/0.99  --comb_inst_mult                        10
% 2.91/0.99  
% 2.91/0.99  ------ Debug Options
% 2.91/0.99  
% 2.91/0.99  --dbg_backtrace                         false
% 2.91/0.99  --dbg_dump_prop_clauses                 false
% 2.91/0.99  --dbg_dump_prop_clauses_file            -
% 2.91/0.99  --dbg_out_stat                          false
% 2.91/0.99  
% 2.91/0.99  
% 2.91/0.99  
% 2.91/0.99  
% 2.91/0.99  ------ Proving...
% 2.91/0.99  
% 2.91/0.99  
% 2.91/0.99  % SZS status Theorem for theBenchmark.p
% 2.91/0.99  
% 2.91/0.99   Resolution empty clause
% 2.91/0.99  
% 2.91/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.91/0.99  
% 2.91/0.99  fof(f1,axiom,(
% 2.91/0.99    v1_xboole_0(k1_xboole_0)),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f46,plain,(
% 2.91/0.99    v1_xboole_0(k1_xboole_0)),
% 2.91/0.99    inference(cnf_transformation,[],[f1])).
% 2.91/0.99  
% 2.91/0.99  fof(f14,axiom,(
% 2.91/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f22,plain,(
% 2.91/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.91/0.99    inference(ennf_transformation,[],[f14])).
% 2.91/0.99  
% 2.91/0.99  fof(f23,plain,(
% 2.91/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.91/0.99    inference(flattening,[],[f22])).
% 2.91/0.99  
% 2.91/0.99  fof(f75,plain,(
% 2.91/0.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f23])).
% 2.91/0.99  
% 2.91/0.99  fof(f17,conjecture,(
% 2.91/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f18,negated_conjecture,(
% 2.91/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.91/0.99    inference(negated_conjecture,[],[f17])).
% 2.91/0.99  
% 2.91/0.99  fof(f28,plain,(
% 2.91/0.99    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.91/0.99    inference(ennf_transformation,[],[f18])).
% 2.91/0.99  
% 2.91/0.99  fof(f29,plain,(
% 2.91/0.99    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 2.91/0.99    inference(flattening,[],[f28])).
% 2.91/0.99  
% 2.91/0.99  fof(f44,plain,(
% 2.91/0.99    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK4),X0) & m1_subset_1(sK4,X0))) )),
% 2.91/0.99    introduced(choice_axiom,[])).
% 2.91/0.99  
% 2.91/0.99  fof(f43,plain,(
% 2.91/0.99    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,X1),sK3) & m1_subset_1(X1,sK3)) & ~v1_xboole_0(sK3))),
% 2.91/0.99    introduced(choice_axiom,[])).
% 2.91/0.99  
% 2.91/0.99  fof(f45,plain,(
% 2.91/0.99    (v1_zfmisc_1(sK3) & v1_subset_1(k6_domain_1(sK3,sK4),sK3) & m1_subset_1(sK4,sK3)) & ~v1_xboole_0(sK3)),
% 2.91/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f44,f43])).
% 2.91/0.99  
% 2.91/0.99  fof(f80,plain,(
% 2.91/0.99    v1_subset_1(k6_domain_1(sK3,sK4),sK3)),
% 2.91/0.99    inference(cnf_transformation,[],[f45])).
% 2.91/0.99  
% 2.91/0.99  fof(f16,axiom,(
% 2.91/0.99    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f26,plain,(
% 2.91/0.99    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.91/0.99    inference(ennf_transformation,[],[f16])).
% 2.91/0.99  
% 2.91/0.99  fof(f27,plain,(
% 2.91/0.99    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.91/0.99    inference(flattening,[],[f26])).
% 2.91/0.99  
% 2.91/0.99  fof(f77,plain,(
% 2.91/0.99    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f27])).
% 2.91/0.99  
% 2.91/0.99  fof(f13,axiom,(
% 2.91/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f21,plain,(
% 2.91/0.99    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.91/0.99    inference(ennf_transformation,[],[f13])).
% 2.91/0.99  
% 2.91/0.99  fof(f74,plain,(
% 2.91/0.99    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f21])).
% 2.91/0.99  
% 2.91/0.99  fof(f81,plain,(
% 2.91/0.99    v1_zfmisc_1(sK3)),
% 2.91/0.99    inference(cnf_transformation,[],[f45])).
% 2.91/0.99  
% 2.91/0.99  fof(f78,plain,(
% 2.91/0.99    ~v1_xboole_0(sK3)),
% 2.91/0.99    inference(cnf_transformation,[],[f45])).
% 2.91/0.99  
% 2.91/0.99  fof(f79,plain,(
% 2.91/0.99    m1_subset_1(sK4,sK3)),
% 2.91/0.99    inference(cnf_transformation,[],[f45])).
% 2.91/0.99  
% 2.91/0.99  fof(f2,axiom,(
% 2.91/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f19,plain,(
% 2.91/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.91/0.99    inference(ennf_transformation,[],[f2])).
% 2.91/0.99  
% 2.91/0.99  fof(f47,plain,(
% 2.91/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f19])).
% 2.91/0.99  
% 2.91/0.99  fof(f15,axiom,(
% 2.91/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f24,plain,(
% 2.91/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.91/0.99    inference(ennf_transformation,[],[f15])).
% 2.91/0.99  
% 2.91/0.99  fof(f25,plain,(
% 2.91/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.91/0.99    inference(flattening,[],[f24])).
% 2.91/0.99  
% 2.91/0.99  fof(f76,plain,(
% 2.91/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f25])).
% 2.91/0.99  
% 2.91/0.99  fof(f3,axiom,(
% 2.91/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f48,plain,(
% 2.91/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f3])).
% 2.91/0.99  
% 2.91/0.99  fof(f4,axiom,(
% 2.91/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f49,plain,(
% 2.91/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f4])).
% 2.91/0.99  
% 2.91/0.99  fof(f5,axiom,(
% 2.91/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f50,plain,(
% 2.91/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f5])).
% 2.91/0.99  
% 2.91/0.99  fof(f6,axiom,(
% 2.91/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f51,plain,(
% 2.91/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f6])).
% 2.91/0.99  
% 2.91/0.99  fof(f7,axiom,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f52,plain,(
% 2.91/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f7])).
% 2.91/0.99  
% 2.91/0.99  fof(f8,axiom,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f53,plain,(
% 2.91/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f8])).
% 2.91/0.99  
% 2.91/0.99  fof(f9,axiom,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f54,plain,(
% 2.91/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f9])).
% 2.91/0.99  
% 2.91/0.99  fof(f82,plain,(
% 2.91/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.91/0.99    inference(definition_unfolding,[],[f53,f54])).
% 2.91/0.99  
% 2.91/0.99  fof(f83,plain,(
% 2.91/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.91/0.99    inference(definition_unfolding,[],[f52,f82])).
% 2.91/0.99  
% 2.91/0.99  fof(f84,plain,(
% 2.91/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.91/0.99    inference(definition_unfolding,[],[f51,f83])).
% 2.91/0.99  
% 2.91/0.99  fof(f85,plain,(
% 2.91/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.91/0.99    inference(definition_unfolding,[],[f50,f84])).
% 2.91/0.99  
% 2.91/0.99  fof(f86,plain,(
% 2.91/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.91/0.99    inference(definition_unfolding,[],[f49,f85])).
% 2.91/0.99  
% 2.91/0.99  fof(f87,plain,(
% 2.91/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.91/0.99    inference(definition_unfolding,[],[f48,f86])).
% 2.91/0.99  
% 2.91/0.99  fof(f88,plain,(
% 2.91/0.99    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.91/0.99    inference(definition_unfolding,[],[f76,f87])).
% 2.91/0.99  
% 2.91/0.99  fof(f12,axiom,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f20,plain,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 2.91/0.99    inference(ennf_transformation,[],[f12])).
% 2.91/0.99  
% 2.91/0.99  fof(f31,plain,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.91/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.91/0.99  
% 2.91/0.99  fof(f30,plain,(
% 2.91/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.91/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.91/0.99  
% 2.91/0.99  fof(f32,plain,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 2.91/0.99    inference(definition_folding,[],[f20,f31,f30])).
% 2.91/0.99  
% 2.91/0.99  fof(f42,plain,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 2.91/0.99    inference(nnf_transformation,[],[f32])).
% 2.91/0.99  
% 2.91/0.99  fof(f72,plain,(
% 2.91/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 2.91/0.99    inference(cnf_transformation,[],[f42])).
% 2.91/0.99  
% 2.91/0.99  fof(f99,plain,(
% 2.91/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.91/0.99    inference(equality_resolution,[],[f72])).
% 2.91/0.99  
% 2.91/0.99  fof(f39,plain,(
% 2.91/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.91/0.99    inference(nnf_transformation,[],[f30])).
% 2.91/0.99  
% 2.91/0.99  fof(f40,plain,(
% 2.91/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.91/0.99    inference(flattening,[],[f39])).
% 2.91/0.99  
% 2.91/0.99  fof(f41,plain,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.91/0.99    inference(rectify,[],[f40])).
% 2.91/0.99  
% 2.91/0.99  fof(f71,plain,(
% 2.91/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 2.91/0.99    inference(cnf_transformation,[],[f41])).
% 2.91/0.99  
% 2.91/0.99  fof(f91,plain,(
% 2.91/0.99    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.91/0.99    inference(equality_resolution,[],[f71])).
% 2.91/0.99  
% 2.91/0.99  fof(f35,plain,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.91/0.99    inference(nnf_transformation,[],[f31])).
% 2.91/0.99  
% 2.91/0.99  fof(f36,plain,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.91/0.99    inference(rectify,[],[f35])).
% 2.91/0.99  
% 2.91/0.99  fof(f37,plain,(
% 2.91/0.99    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 2.91/0.99    introduced(choice_axiom,[])).
% 2.91/0.99  
% 2.91/0.99  fof(f38,plain,(
% 2.91/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.91/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 2.91/0.99  
% 2.91/0.99  fof(f60,plain,(
% 2.91/0.99    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.91/0.99    inference(cnf_transformation,[],[f38])).
% 2.91/0.99  
% 2.91/0.99  fof(f10,axiom,(
% 2.91/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f33,plain,(
% 2.91/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.91/0.99    inference(nnf_transformation,[],[f10])).
% 2.91/0.99  
% 2.91/0.99  fof(f34,plain,(
% 2.91/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.91/0.99    inference(flattening,[],[f33])).
% 2.91/0.99  
% 2.91/0.99  fof(f57,plain,(
% 2.91/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.91/0.99    inference(cnf_transformation,[],[f34])).
% 2.91/0.99  
% 2.91/0.99  fof(f89,plain,(
% 2.91/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.91/0.99    inference(equality_resolution,[],[f57])).
% 2.91/0.99  
% 2.91/0.99  fof(f11,axiom,(
% 2.91/0.99    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 2.91/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.91/0.99  
% 2.91/0.99  fof(f58,plain,(
% 2.91/0.99    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 2.91/0.99    inference(cnf_transformation,[],[f11])).
% 2.91/0.99  
% 2.91/0.99  cnf(c_0,plain,
% 2.91/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.91/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2143,plain,
% 2.91/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_22,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,X1)
% 2.91/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.91/0.99      | v1_xboole_0(X1) ),
% 2.91/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2125,plain,
% 2.91/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.91/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.91/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_26,negated_conjecture,
% 2.91/0.99      ( v1_subset_1(k6_domain_1(sK3,sK4),sK3) ),
% 2.91/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_24,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.91/0.99      | ~ v1_subset_1(X0,X1)
% 2.91/0.99      | ~ v1_zfmisc_1(X1)
% 2.91/0.99      | v1_xboole_0(X0)
% 2.91/0.99      | v1_xboole_0(X1) ),
% 2.91/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_21,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.91/0.99      | ~ v1_subset_1(X0,X1)
% 2.91/0.99      | ~ v1_xboole_0(X1) ),
% 2.91/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_140,plain,
% 2.91/0.99      ( v1_xboole_0(X0)
% 2.91/0.99      | ~ v1_zfmisc_1(X1)
% 2.91/0.99      | ~ v1_subset_1(X0,X1)
% 2.91/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.91/0.99      inference(global_propositional_subsumption,[status(thm)],[c_24,c_21]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_141,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.91/0.99      | ~ v1_subset_1(X0,X1)
% 2.91/0.99      | ~ v1_zfmisc_1(X1)
% 2.91/0.99      | v1_xboole_0(X0) ),
% 2.91/0.99      inference(renaming,[status(thm)],[c_140]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_25,negated_conjecture,
% 2.91/0.99      ( v1_zfmisc_1(sK3) ),
% 2.91/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_282,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.91/0.99      | ~ v1_subset_1(X0,X1)
% 2.91/0.99      | v1_xboole_0(X0)
% 2.91/0.99      | sK3 != X1 ),
% 2.91/0.99      inference(resolution_lifted,[status(thm)],[c_141,c_25]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_283,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 2.91/0.99      | ~ v1_subset_1(X0,sK3)
% 2.91/0.99      | v1_xboole_0(X0) ),
% 2.91/0.99      inference(unflattening,[status(thm)],[c_282]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_301,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
% 2.91/0.99      | v1_xboole_0(X0)
% 2.91/0.99      | k6_domain_1(sK3,sK4) != X0
% 2.91/0.99      | sK3 != sK3 ),
% 2.91/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_283]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_302,plain,
% 2.91/0.99      ( ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
% 2.91/0.99      | v1_xboole_0(k6_domain_1(sK3,sK4)) ),
% 2.91/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2121,plain,
% 2.91/0.99      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
% 2.91/0.99      | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_3212,plain,
% 2.91/0.99      ( m1_subset_1(sK4,sK3) != iProver_top
% 2.91/0.99      | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top
% 2.91/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.91/0.99      inference(superposition,[status(thm)],[c_2125,c_2121]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_28,negated_conjecture,
% 2.91/0.99      ( ~ v1_xboole_0(sK3) ),
% 2.91/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_29,plain,
% 2.91/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_27,negated_conjecture,
% 2.91/0.99      ( m1_subset_1(sK4,sK3) ),
% 2.91/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_30,plain,
% 2.91/0.99      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_303,plain,
% 2.91/0.99      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top
% 2.91/0.99      | v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2304,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,sK3)
% 2.91/0.99      | m1_subset_1(k6_domain_1(sK3,X0),k1_zfmisc_1(sK3))
% 2.91/0.99      | v1_xboole_0(sK3) ),
% 2.91/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2348,plain,
% 2.91/0.99      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
% 2.91/0.99      | ~ m1_subset_1(sK4,sK3)
% 2.91/0.99      | v1_xboole_0(sK3) ),
% 2.91/0.99      inference(instantiation,[status(thm)],[c_2304]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2349,plain,
% 2.91/0.99      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
% 2.91/0.99      | m1_subset_1(sK4,sK3) != iProver_top
% 2.91/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_2348]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_4055,plain,
% 2.91/0.99      ( v1_xboole_0(k6_domain_1(sK3,sK4)) = iProver_top ),
% 2.91/0.99      inference(global_propositional_subsumption,
% 2.91/0.99                [status(thm)],
% 2.91/0.99                [c_3212,c_29,c_30,c_303,c_2349]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_1,plain,
% 2.91/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.91/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2142,plain,
% 2.91/0.99      ( X0 = X1
% 2.91/0.99      | v1_xboole_0(X1) != iProver_top
% 2.91/0.99      | v1_xboole_0(X0) != iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_4060,plain,
% 2.91/0.99      ( k6_domain_1(sK3,sK4) = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.91/0.99      inference(superposition,[status(thm)],[c_4055,c_2142]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_4067,plain,
% 2.91/0.99      ( k6_domain_1(sK3,sK4) = k1_xboole_0 ),
% 2.91/0.99      inference(superposition,[status(thm)],[c_2143,c_4060]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2123,plain,
% 2.91/0.99      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_23,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,X1)
% 2.91/0.99      | v1_xboole_0(X1)
% 2.91/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.91/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2124,plain,
% 2.91/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
% 2.91/0.99      | m1_subset_1(X0,X1) != iProver_top
% 2.91/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2434,plain,
% 2.91/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(sK3,sK4)
% 2.91/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 2.91/0.99      inference(superposition,[status(thm)],[c_2123,c_2124]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2314,plain,
% 2.91/0.99      ( ~ m1_subset_1(X0,sK3)
% 2.91/0.99      | v1_xboole_0(sK3)
% 2.91/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(sK3,X0) ),
% 2.91/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2394,plain,
% 2.91/0.99      ( ~ m1_subset_1(sK4,sK3)
% 2.91/0.99      | v1_xboole_0(sK3)
% 2.91/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
% 2.91/0.99      inference(instantiation,[status(thm)],[c_2314]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2676,plain,
% 2.91/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_domain_1(sK3,sK4) ),
% 2.91/0.99      inference(global_propositional_subsumption,
% 2.91/0.99                [status(thm)],
% 2.91/0.99                [c_2434,c_28,c_27,c_2394]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_20,plain,
% 2.91/0.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.91/0.99      inference(cnf_transformation,[],[f99]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2126,plain,
% 2.91/0.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_3231,plain,
% 2.91/0.99      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_domain_1(sK3,sK4)) = iProver_top ),
% 2.91/0.99      inference(superposition,[status(thm)],[c_2676,c_2126]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_4375,plain,
% 2.91/0.99      ( sP1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0) = iProver_top ),
% 2.91/0.99      inference(demodulation,[status(thm)],[c_4067,c_3231]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_10,plain,
% 2.91/0.99      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 2.91/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2136,plain,
% 2.91/0.99      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_8,plain,
% 2.91/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.91/0.99      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 2.91/0.99      | r2_hidden(X0,X9) ),
% 2.91/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2138,plain,
% 2.91/0.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.91/0.99      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 2.91/0.99      | r2_hidden(X0,X9) = iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_3854,plain,
% 2.91/0.99      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 2.91/0.99      | r2_hidden(X7,X8) = iProver_top ),
% 2.91/0.99      inference(superposition,[status(thm)],[c_2136,c_2138]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_7590,plain,
% 2.91/0.99      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 2.91/0.99      inference(superposition,[status(thm)],[c_4375,c_3854]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2,plain,
% 2.91/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.91/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_5,plain,
% 2.91/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 2.91/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2141,plain,
% 2.91/0.99      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.91/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_2383,plain,
% 2.91/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.91/0.99      inference(superposition,[status(thm)],[c_2,c_2141]) ).
% 2.91/0.99  
% 2.91/0.99  cnf(c_8416,plain,
% 2.91/0.99      ( $false ),
% 2.91/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_7590,c_2383]) ).
% 2.91/0.99  
% 2.91/0.99  
% 2.91/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.91/0.99  
% 2.91/0.99  ------                               Statistics
% 2.91/0.99  
% 2.91/0.99  ------ General
% 2.91/0.99  
% 2.91/0.99  abstr_ref_over_cycles:                  0
% 2.91/0.99  abstr_ref_under_cycles:                 0
% 2.91/0.99  gc_basic_clause_elim:                   0
% 2.91/0.99  forced_gc_time:                         0
% 2.91/0.99  parsing_time:                           0.01
% 2.91/0.99  unif_index_cands_time:                  0.
% 2.91/0.99  unif_index_add_time:                    0.
% 2.91/0.99  orderings_time:                         0.
% 2.91/0.99  out_proof_time:                         0.012
% 2.91/0.99  total_time:                             0.332
% 2.91/0.99  num_of_symbols:                         46
% 2.91/0.99  num_of_terms:                           12317
% 2.91/0.99  
% 2.91/0.99  ------ Preprocessing
% 2.91/0.99  
% 2.91/0.99  num_of_splits:                          0
% 2.91/0.99  num_of_split_atoms:                     0
% 2.91/0.99  num_of_reused_defs:                     0
% 2.91/0.99  num_eq_ax_congr_red:                    100
% 2.91/0.99  num_of_sem_filtered_clauses:            1
% 2.91/0.99  num_of_subtypes:                        0
% 2.91/0.99  monotx_restored_types:                  0
% 2.91/0.99  sat_num_of_epr_types:                   0
% 2.91/0.99  sat_num_of_non_cyclic_types:            0
% 2.91/0.99  sat_guarded_non_collapsed_types:        0
% 2.91/0.99  num_pure_diseq_elim:                    0
% 2.91/0.99  simp_replaced_by:                       0
% 2.91/0.99  res_preprocessed:                       128
% 2.91/0.99  prep_upred:                             0
% 2.91/0.99  prep_unflattend:                        614
% 2.91/0.99  smt_new_axioms:                         0
% 2.91/0.99  pred_elim_cands:                        5
% 2.91/0.99  pred_elim:                              2
% 2.91/0.99  pred_elim_cl:                           3
% 2.91/0.99  pred_elim_cycles:                       8
% 2.91/0.99  merged_defs:                            0
% 2.91/0.99  merged_defs_ncl:                        0
% 2.91/0.99  bin_hyper_res:                          0
% 2.91/0.99  prep_cycles:                            4
% 2.91/0.99  pred_elim_time:                         0.026
% 2.91/0.99  splitting_time:                         0.
% 2.91/0.99  sem_filter_time:                        0.
% 2.91/0.99  monotx_time:                            0.001
% 2.91/0.99  subtype_inf_time:                       0.
% 2.91/0.99  
% 2.91/0.99  ------ Problem properties
% 2.91/0.99  
% 2.91/0.99  clauses:                                26
% 2.91/0.99  conjectures:                            2
% 2.91/0.99  epr:                                    15
% 2.91/0.99  horn:                                   21
% 2.91/0.99  ground:                                 4
% 2.91/0.99  unary:                                  15
% 2.91/0.99  binary:                                 2
% 2.91/0.99  lits:                                   52
% 2.91/0.99  lits_eq:                                16
% 2.91/0.99  fd_pure:                                0
% 2.91/0.99  fd_pseudo:                              0
% 2.91/0.99  fd_cond:                                1
% 2.91/0.99  fd_pseudo_cond:                         3
% 2.91/0.99  ac_symbols:                             0
% 2.91/0.99  
% 2.91/0.99  ------ Propositional Solver
% 2.91/0.99  
% 2.91/0.99  prop_solver_calls:                      30
% 2.91/0.99  prop_fast_solver_calls:                 894
% 2.91/0.99  smt_solver_calls:                       0
% 2.91/0.99  smt_fast_solver_calls:                  0
% 2.91/0.99  prop_num_of_clauses:                    2745
% 2.91/0.99  prop_preprocess_simplified:             10245
% 2.91/0.99  prop_fo_subsumed:                       6
% 2.91/0.99  prop_solver_time:                       0.
% 2.91/0.99  smt_solver_time:                        0.
% 2.91/0.99  smt_fast_solver_time:                   0.
% 2.91/0.99  prop_fast_solver_time:                  0.
% 2.91/0.99  prop_unsat_core_time:                   0.
% 2.91/0.99  
% 2.91/0.99  ------ QBF
% 2.91/0.99  
% 2.91/0.99  qbf_q_res:                              0
% 2.91/0.99  qbf_num_tautologies:                    0
% 2.91/0.99  qbf_prep_cycles:                        0
% 2.91/0.99  
% 2.91/0.99  ------ BMC1
% 2.91/0.99  
% 2.91/0.99  bmc1_current_bound:                     -1
% 2.91/0.99  bmc1_last_solved_bound:                 -1
% 2.91/0.99  bmc1_unsat_core_size:                   -1
% 2.91/0.99  bmc1_unsat_core_parents_size:           -1
% 2.91/0.99  bmc1_merge_next_fun:                    0
% 2.91/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.91/0.99  
% 2.91/0.99  ------ Instantiation
% 2.91/0.99  
% 2.91/0.99  inst_num_of_clauses:                    998
% 2.91/0.99  inst_num_in_passive:                    406
% 2.91/0.99  inst_num_in_active:                     224
% 2.91/0.99  inst_num_in_unprocessed:                368
% 2.91/0.99  inst_num_of_loops:                      250
% 2.91/0.99  inst_num_of_learning_restarts:          0
% 2.91/0.99  inst_num_moves_active_passive:          23
% 2.91/0.99  inst_lit_activity:                      0
% 2.91/0.99  inst_lit_activity_moves:                0
% 2.91/0.99  inst_num_tautologies:                   0
% 2.91/0.99  inst_num_prop_implied:                  0
% 2.91/0.99  inst_num_existing_simplified:           0
% 2.91/0.99  inst_num_eq_res_simplified:             0
% 2.91/0.99  inst_num_child_elim:                    0
% 2.91/0.99  inst_num_of_dismatching_blockings:      618
% 2.91/0.99  inst_num_of_non_proper_insts:           986
% 2.91/0.99  inst_num_of_duplicates:                 0
% 2.91/0.99  inst_inst_num_from_inst_to_res:         0
% 2.91/0.99  inst_dismatching_checking_time:         0.
% 2.91/0.99  
% 2.91/0.99  ------ Resolution
% 2.91/0.99  
% 2.91/0.99  res_num_of_clauses:                     0
% 2.91/0.99  res_num_in_passive:                     0
% 2.91/0.99  res_num_in_active:                      0
% 2.91/0.99  res_num_of_loops:                       132
% 2.91/0.99  res_forward_subset_subsumed:            315
% 2.91/0.99  res_backward_subset_subsumed:           0
% 2.91/0.99  res_forward_subsumed:                   0
% 2.91/0.99  res_backward_subsumed:                  0
% 2.91/0.99  res_forward_subsumption_resolution:     0
% 2.91/0.99  res_backward_subsumption_resolution:    0
% 2.91/0.99  res_clause_to_clause_subsumption:       1201
% 2.91/0.99  res_orphan_elimination:                 0
% 2.91/0.99  res_tautology_del:                      73
% 2.91/0.99  res_num_eq_res_simplified:              0
% 2.91/0.99  res_num_sel_changes:                    0
% 2.91/0.99  res_moves_from_active_to_pass:          0
% 2.91/0.99  
% 2.91/0.99  ------ Superposition
% 2.91/0.99  
% 2.91/0.99  sup_time_total:                         0.
% 2.91/0.99  sup_time_generating:                    0.
% 2.91/0.99  sup_time_sim_full:                      0.
% 2.91/0.99  sup_time_sim_immed:                     0.
% 2.91/0.99  
% 2.91/0.99  sup_num_of_clauses:                     66
% 2.91/0.99  sup_num_in_active:                      42
% 2.91/0.99  sup_num_in_passive:                     24
% 2.91/0.99  sup_num_of_loops:                       48
% 2.91/0.99  sup_fw_superposition:                   45
% 2.91/0.99  sup_bw_superposition:                   22
% 2.91/0.99  sup_immediate_simplified:               4
% 2.91/0.99  sup_given_eliminated:                   1
% 2.91/0.99  comparisons_done:                       0
% 2.91/0.99  comparisons_avoided:                    4
% 2.91/0.99  
% 2.91/0.99  ------ Simplifications
% 2.91/0.99  
% 2.91/0.99  
% 2.91/0.99  sim_fw_subset_subsumed:                 2
% 2.91/0.99  sim_bw_subset_subsumed:                 0
% 2.91/0.99  sim_fw_subsumed:                        2
% 2.91/0.99  sim_bw_subsumed:                        1
% 2.91/0.99  sim_fw_subsumption_res:                 1
% 2.91/0.99  sim_bw_subsumption_res:                 0
% 2.91/0.99  sim_tautology_del:                      1
% 2.91/0.99  sim_eq_tautology_del:                   6
% 2.91/0.99  sim_eq_res_simp:                        0
% 2.91/0.99  sim_fw_demodulated:                     0
% 2.91/0.99  sim_bw_demodulated:                     6
% 2.91/0.99  sim_light_normalised:                   2
% 2.91/0.99  sim_joinable_taut:                      0
% 2.91/0.99  sim_joinable_simp:                      0
% 2.91/0.99  sim_ac_normalised:                      0
% 2.91/0.99  sim_smt_subsumption:                    0
% 2.91/0.99  
%------------------------------------------------------------------------------
