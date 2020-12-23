%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:30 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 289 expanded)
%              Number of clauses        :   36 (  47 expanded)
%              Number of leaves         :   18 (  77 expanded)
%              Depth                    :   20
%              Number of atoms          :  375 ( 827 expanded)
%              Number of equality atoms :  192 ( 391 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK7,sK6) != sK5
      & r2_hidden(sK6,sK4)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
      & v1_funct_2(sK7,sK4,k1_tarski(sK5))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k1_funct_1(sK7,sK6) != sK5
    & r2_hidden(sK6,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))
    & v1_funct_2(sK7,sK4,k1_tarski(sK5))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f19,f36])).

fof(f69,plain,(
    v1_funct_2(sK7,sK4,k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f75])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f76])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f77])).

fof(f86,plain,(
    v1_funct_2(sK7,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f70,f78])).

fof(f68,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f78])).

fof(f89,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f82])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
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

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f15,f21,f20])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f65])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f50,f78,f78])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f97,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f57])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK7,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_342,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_343,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK7,X2),X1)
    | ~ v1_funct_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_347,plain,
    ( r2_hidden(k1_funct_1(sK7,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK7,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_27])).

cnf(c_348,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK7,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_375,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK7,X0),X2)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X2
    | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X1
    | sK7 != sK7
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_348])).

cnf(c_376,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k1_funct_1(sK7,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_960,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(k1_funct_1(sK7,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(equality_resolution_simp,[status(thm)],[c_376])).

cnf(c_2200,plain,
    ( k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_960])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK6,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_23,negated_conjecture,
    ( k1_funct_1(sK7,sK6) != sK5 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2374,plain,
    ( r2_hidden(k1_funct_1(sK7,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK6,sK4)
    | k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2386,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k1_funct_1(sK7,sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2414,plain,
    ( k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2200,c_24,c_23,c_2374,c_2386])).

cnf(c_21,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2202,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2544,plain,
    ( sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_2202])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2464,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,k1_xboole_0)
    | r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2465,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,k1_xboole_0) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2464])).

cnf(c_2467,plain,
    ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != iProver_top
    | sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,k1_xboole_0) != iProver_top
    | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2465])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2395,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2400,plain,
    ( k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_xboole_0) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2395])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2394,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2396,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2394])).

cnf(c_2398,plain,
    ( k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_xboole_0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | r2_hidden(sK5,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2396])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_44,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_46,plain,
    ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2544,c_2467,c_2400,c_2398,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:49:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.52/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.52/0.97  
% 1.52/0.97  ------  iProver source info
% 1.52/0.97  
% 1.52/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.52/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.52/0.97  git: non_committed_changes: false
% 1.52/0.97  git: last_make_outside_of_git: false
% 1.52/0.97  
% 1.52/0.97  ------ 
% 1.52/0.97  
% 1.52/0.97  ------ Input Options
% 1.52/0.97  
% 1.52/0.97  --out_options                           all
% 1.52/0.97  --tptp_safe_out                         true
% 1.52/0.97  --problem_path                          ""
% 1.52/0.97  --include_path                          ""
% 1.52/0.97  --clausifier                            res/vclausify_rel
% 1.52/0.97  --clausifier_options                    --mode clausify
% 1.52/0.97  --stdin                                 false
% 1.52/0.97  --stats_out                             all
% 1.52/0.97  
% 1.52/0.97  ------ General Options
% 1.52/0.97  
% 1.52/0.97  --fof                                   false
% 1.52/0.97  --time_out_real                         305.
% 1.52/0.97  --time_out_virtual                      -1.
% 1.52/0.97  --symbol_type_check                     false
% 1.52/0.97  --clausify_out                          false
% 1.52/0.97  --sig_cnt_out                           false
% 1.52/0.97  --trig_cnt_out                          false
% 1.52/0.97  --trig_cnt_out_tolerance                1.
% 1.52/0.97  --trig_cnt_out_sk_spl                   false
% 1.52/0.97  --abstr_cl_out                          false
% 1.52/0.97  
% 1.52/0.97  ------ Global Options
% 1.52/0.97  
% 1.52/0.97  --schedule                              default
% 1.52/0.97  --add_important_lit                     false
% 1.52/0.97  --prop_solver_per_cl                    1000
% 1.52/0.97  --min_unsat_core                        false
% 1.52/0.97  --soft_assumptions                      false
% 1.52/0.97  --soft_lemma_size                       3
% 1.52/0.97  --prop_impl_unit_size                   0
% 1.52/0.97  --prop_impl_unit                        []
% 1.52/0.97  --share_sel_clauses                     true
% 1.52/0.97  --reset_solvers                         false
% 1.52/0.97  --bc_imp_inh                            [conj_cone]
% 1.52/0.97  --conj_cone_tolerance                   3.
% 1.52/0.97  --extra_neg_conj                        none
% 1.52/0.97  --large_theory_mode                     true
% 1.52/0.97  --prolific_symb_bound                   200
% 1.52/0.97  --lt_threshold                          2000
% 1.52/0.97  --clause_weak_htbl                      true
% 1.52/0.97  --gc_record_bc_elim                     false
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing Options
% 1.52/0.97  
% 1.52/0.97  --preprocessing_flag                    true
% 1.52/0.97  --time_out_prep_mult                    0.1
% 1.52/0.97  --splitting_mode                        input
% 1.52/0.97  --splitting_grd                         true
% 1.52/0.97  --splitting_cvd                         false
% 1.52/0.97  --splitting_cvd_svl                     false
% 1.52/0.97  --splitting_nvd                         32
% 1.52/0.97  --sub_typing                            true
% 1.52/0.97  --prep_gs_sim                           true
% 1.52/0.97  --prep_unflatten                        true
% 1.52/0.97  --prep_res_sim                          true
% 1.52/0.97  --prep_upred                            true
% 1.52/0.97  --prep_sem_filter                       exhaustive
% 1.52/0.97  --prep_sem_filter_out                   false
% 1.52/0.97  --pred_elim                             true
% 1.52/0.97  --res_sim_input                         true
% 1.52/0.97  --eq_ax_congr_red                       true
% 1.52/0.97  --pure_diseq_elim                       true
% 1.52/0.97  --brand_transform                       false
% 1.52/0.97  --non_eq_to_eq                          false
% 1.52/0.97  --prep_def_merge                        true
% 1.52/0.97  --prep_def_merge_prop_impl              false
% 1.52/0.97  --prep_def_merge_mbd                    true
% 1.52/0.97  --prep_def_merge_tr_red                 false
% 1.52/0.97  --prep_def_merge_tr_cl                  false
% 1.52/0.97  --smt_preprocessing                     true
% 1.52/0.97  --smt_ac_axioms                         fast
% 1.52/0.97  --preprocessed_out                      false
% 1.52/0.97  --preprocessed_stats                    false
% 1.52/0.97  
% 1.52/0.97  ------ Abstraction refinement Options
% 1.52/0.97  
% 1.52/0.97  --abstr_ref                             []
% 1.52/0.97  --abstr_ref_prep                        false
% 1.52/0.97  --abstr_ref_until_sat                   false
% 1.52/0.97  --abstr_ref_sig_restrict                funpre
% 1.52/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.97  --abstr_ref_under                       []
% 1.52/0.97  
% 1.52/0.97  ------ SAT Options
% 1.52/0.97  
% 1.52/0.97  --sat_mode                              false
% 1.52/0.97  --sat_fm_restart_options                ""
% 1.52/0.97  --sat_gr_def                            false
% 1.52/0.97  --sat_epr_types                         true
% 1.52/0.97  --sat_non_cyclic_types                  false
% 1.52/0.97  --sat_finite_models                     false
% 1.52/0.97  --sat_fm_lemmas                         false
% 1.52/0.97  --sat_fm_prep                           false
% 1.52/0.97  --sat_fm_uc_incr                        true
% 1.52/0.97  --sat_out_model                         small
% 1.52/0.97  --sat_out_clauses                       false
% 1.52/0.97  
% 1.52/0.97  ------ QBF Options
% 1.52/0.97  
% 1.52/0.97  --qbf_mode                              false
% 1.52/0.97  --qbf_elim_univ                         false
% 1.52/0.97  --qbf_dom_inst                          none
% 1.52/0.97  --qbf_dom_pre_inst                      false
% 1.52/0.97  --qbf_sk_in                             false
% 1.52/0.97  --qbf_pred_elim                         true
% 1.52/0.97  --qbf_split                             512
% 1.52/0.97  
% 1.52/0.97  ------ BMC1 Options
% 1.52/0.97  
% 1.52/0.97  --bmc1_incremental                      false
% 1.52/0.97  --bmc1_axioms                           reachable_all
% 1.52/0.97  --bmc1_min_bound                        0
% 1.52/0.97  --bmc1_max_bound                        -1
% 1.52/0.97  --bmc1_max_bound_default                -1
% 1.52/0.97  --bmc1_symbol_reachability              true
% 1.52/0.97  --bmc1_property_lemmas                  false
% 1.52/0.97  --bmc1_k_induction                      false
% 1.52/0.97  --bmc1_non_equiv_states                 false
% 1.52/0.97  --bmc1_deadlock                         false
% 1.52/0.97  --bmc1_ucm                              false
% 1.52/0.97  --bmc1_add_unsat_core                   none
% 1.52/0.97  --bmc1_unsat_core_children              false
% 1.52/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.97  --bmc1_out_stat                         full
% 1.52/0.97  --bmc1_ground_init                      false
% 1.52/0.97  --bmc1_pre_inst_next_state              false
% 1.52/0.97  --bmc1_pre_inst_state                   false
% 1.52/0.97  --bmc1_pre_inst_reach_state             false
% 1.52/0.97  --bmc1_out_unsat_core                   false
% 1.52/0.97  --bmc1_aig_witness_out                  false
% 1.52/0.97  --bmc1_verbose                          false
% 1.52/0.97  --bmc1_dump_clauses_tptp                false
% 1.52/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.97  --bmc1_dump_file                        -
% 1.52/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.97  --bmc1_ucm_extend_mode                  1
% 1.52/0.97  --bmc1_ucm_init_mode                    2
% 1.52/0.97  --bmc1_ucm_cone_mode                    none
% 1.52/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.97  --bmc1_ucm_relax_model                  4
% 1.52/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.97  --bmc1_ucm_layered_model                none
% 1.52/0.97  --bmc1_ucm_max_lemma_size               10
% 1.52/0.97  
% 1.52/0.97  ------ AIG Options
% 1.52/0.97  
% 1.52/0.97  --aig_mode                              false
% 1.52/0.97  
% 1.52/0.97  ------ Instantiation Options
% 1.52/0.97  
% 1.52/0.97  --instantiation_flag                    true
% 1.52/0.97  --inst_sos_flag                         false
% 1.52/0.97  --inst_sos_phase                        true
% 1.52/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel_side                     num_symb
% 1.52/0.97  --inst_solver_per_active                1400
% 1.52/0.97  --inst_solver_calls_frac                1.
% 1.52/0.97  --inst_passive_queue_type               priority_queues
% 1.52/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.97  --inst_passive_queues_freq              [25;2]
% 1.52/0.97  --inst_dismatching                      true
% 1.52/0.97  --inst_eager_unprocessed_to_passive     true
% 1.52/0.97  --inst_prop_sim_given                   true
% 1.52/0.97  --inst_prop_sim_new                     false
% 1.52/0.97  --inst_subs_new                         false
% 1.52/0.97  --inst_eq_res_simp                      false
% 1.52/0.97  --inst_subs_given                       false
% 1.52/0.97  --inst_orphan_elimination               true
% 1.52/0.97  --inst_learning_loop_flag               true
% 1.52/0.97  --inst_learning_start                   3000
% 1.52/0.97  --inst_learning_factor                  2
% 1.52/0.97  --inst_start_prop_sim_after_learn       3
% 1.52/0.97  --inst_sel_renew                        solver
% 1.52/0.97  --inst_lit_activity_flag                true
% 1.52/0.97  --inst_restr_to_given                   false
% 1.52/0.97  --inst_activity_threshold               500
% 1.52/0.97  --inst_out_proof                        true
% 1.52/0.97  
% 1.52/0.97  ------ Resolution Options
% 1.52/0.97  
% 1.52/0.97  --resolution_flag                       true
% 1.52/0.97  --res_lit_sel                           adaptive
% 1.52/0.97  --res_lit_sel_side                      none
% 1.52/0.97  --res_ordering                          kbo
% 1.52/0.97  --res_to_prop_solver                    active
% 1.52/0.97  --res_prop_simpl_new                    false
% 1.52/0.97  --res_prop_simpl_given                  true
% 1.52/0.97  --res_passive_queue_type                priority_queues
% 1.52/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.97  --res_passive_queues_freq               [15;5]
% 1.52/0.97  --res_forward_subs                      full
% 1.52/0.97  --res_backward_subs                     full
% 1.52/0.97  --res_forward_subs_resolution           true
% 1.52/0.97  --res_backward_subs_resolution          true
% 1.52/0.97  --res_orphan_elimination                true
% 1.52/0.97  --res_time_limit                        2.
% 1.52/0.97  --res_out_proof                         true
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Options
% 1.52/0.97  
% 1.52/0.97  --superposition_flag                    true
% 1.52/0.97  --sup_passive_queue_type                priority_queues
% 1.52/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.97  --demod_completeness_check              fast
% 1.52/0.97  --demod_use_ground                      true
% 1.52/0.97  --sup_to_prop_solver                    passive
% 1.52/0.97  --sup_prop_simpl_new                    true
% 1.52/0.97  --sup_prop_simpl_given                  true
% 1.52/0.97  --sup_fun_splitting                     false
% 1.52/0.97  --sup_smt_interval                      50000
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Simplification Setup
% 1.52/0.97  
% 1.52/0.97  --sup_indices_passive                   []
% 1.52/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_full_bw                           [BwDemod]
% 1.52/0.97  --sup_immed_triv                        [TrivRules]
% 1.52/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_immed_bw_main                     []
% 1.52/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  
% 1.52/0.97  ------ Combination Options
% 1.52/0.97  
% 1.52/0.97  --comb_res_mult                         3
% 1.52/0.97  --comb_sup_mult                         2
% 1.52/0.97  --comb_inst_mult                        10
% 1.52/0.97  
% 1.52/0.97  ------ Debug Options
% 1.52/0.97  
% 1.52/0.97  --dbg_backtrace                         false
% 1.52/0.97  --dbg_dump_prop_clauses                 false
% 1.52/0.97  --dbg_dump_prop_clauses_file            -
% 1.52/0.97  --dbg_out_stat                          false
% 1.52/0.97  ------ Parsing...
% 1.52/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.52/0.97  ------ Proving...
% 1.52/0.97  ------ Problem Properties 
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  clauses                                 25
% 1.52/0.97  conjectures                             2
% 1.52/0.97  EPR                                     12
% 1.52/0.97  Horn                                    20
% 1.52/0.97  unary                                   13
% 1.52/0.97  binary                                  4
% 1.52/0.97  lits                                    51
% 1.52/0.97  lits eq                                 19
% 1.52/0.97  fd_pure                                 0
% 1.52/0.97  fd_pseudo                               0
% 1.52/0.97  fd_cond                                 0
% 1.52/0.97  fd_pseudo_cond                          4
% 1.52/0.97  AC symbols                              0
% 1.52/0.97  
% 1.52/0.97  ------ Schedule dynamic 5 is on 
% 1.52/0.97  
% 1.52/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  ------ 
% 1.52/0.97  Current options:
% 1.52/0.97  ------ 
% 1.52/0.97  
% 1.52/0.97  ------ Input Options
% 1.52/0.97  
% 1.52/0.97  --out_options                           all
% 1.52/0.97  --tptp_safe_out                         true
% 1.52/0.97  --problem_path                          ""
% 1.52/0.97  --include_path                          ""
% 1.52/0.97  --clausifier                            res/vclausify_rel
% 1.52/0.97  --clausifier_options                    --mode clausify
% 1.52/0.97  --stdin                                 false
% 1.52/0.97  --stats_out                             all
% 1.52/0.97  
% 1.52/0.97  ------ General Options
% 1.52/0.97  
% 1.52/0.97  --fof                                   false
% 1.52/0.97  --time_out_real                         305.
% 1.52/0.97  --time_out_virtual                      -1.
% 1.52/0.97  --symbol_type_check                     false
% 1.52/0.97  --clausify_out                          false
% 1.52/0.97  --sig_cnt_out                           false
% 1.52/0.97  --trig_cnt_out                          false
% 1.52/0.97  --trig_cnt_out_tolerance                1.
% 1.52/0.97  --trig_cnt_out_sk_spl                   false
% 1.52/0.97  --abstr_cl_out                          false
% 1.52/0.97  
% 1.52/0.97  ------ Global Options
% 1.52/0.97  
% 1.52/0.97  --schedule                              default
% 1.52/0.97  --add_important_lit                     false
% 1.52/0.97  --prop_solver_per_cl                    1000
% 1.52/0.97  --min_unsat_core                        false
% 1.52/0.97  --soft_assumptions                      false
% 1.52/0.97  --soft_lemma_size                       3
% 1.52/0.97  --prop_impl_unit_size                   0
% 1.52/0.97  --prop_impl_unit                        []
% 1.52/0.97  --share_sel_clauses                     true
% 1.52/0.97  --reset_solvers                         false
% 1.52/0.97  --bc_imp_inh                            [conj_cone]
% 1.52/0.97  --conj_cone_tolerance                   3.
% 1.52/0.97  --extra_neg_conj                        none
% 1.52/0.97  --large_theory_mode                     true
% 1.52/0.97  --prolific_symb_bound                   200
% 1.52/0.97  --lt_threshold                          2000
% 1.52/0.97  --clause_weak_htbl                      true
% 1.52/0.97  --gc_record_bc_elim                     false
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing Options
% 1.52/0.97  
% 1.52/0.97  --preprocessing_flag                    true
% 1.52/0.97  --time_out_prep_mult                    0.1
% 1.52/0.97  --splitting_mode                        input
% 1.52/0.97  --splitting_grd                         true
% 1.52/0.97  --splitting_cvd                         false
% 1.52/0.97  --splitting_cvd_svl                     false
% 1.52/0.97  --splitting_nvd                         32
% 1.52/0.97  --sub_typing                            true
% 1.52/0.97  --prep_gs_sim                           true
% 1.52/0.97  --prep_unflatten                        true
% 1.52/0.97  --prep_res_sim                          true
% 1.52/0.97  --prep_upred                            true
% 1.52/0.97  --prep_sem_filter                       exhaustive
% 1.52/0.97  --prep_sem_filter_out                   false
% 1.52/0.97  --pred_elim                             true
% 1.52/0.97  --res_sim_input                         true
% 1.52/0.97  --eq_ax_congr_red                       true
% 1.52/0.97  --pure_diseq_elim                       true
% 1.52/0.97  --brand_transform                       false
% 1.52/0.97  --non_eq_to_eq                          false
% 1.52/0.97  --prep_def_merge                        true
% 1.52/0.97  --prep_def_merge_prop_impl              false
% 1.52/0.97  --prep_def_merge_mbd                    true
% 1.52/0.97  --prep_def_merge_tr_red                 false
% 1.52/0.97  --prep_def_merge_tr_cl                  false
% 1.52/0.97  --smt_preprocessing                     true
% 1.52/0.97  --smt_ac_axioms                         fast
% 1.52/0.97  --preprocessed_out                      false
% 1.52/0.97  --preprocessed_stats                    false
% 1.52/0.97  
% 1.52/0.97  ------ Abstraction refinement Options
% 1.52/0.97  
% 1.52/0.97  --abstr_ref                             []
% 1.52/0.97  --abstr_ref_prep                        false
% 1.52/0.97  --abstr_ref_until_sat                   false
% 1.52/0.97  --abstr_ref_sig_restrict                funpre
% 1.52/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.97  --abstr_ref_under                       []
% 1.52/0.97  
% 1.52/0.97  ------ SAT Options
% 1.52/0.97  
% 1.52/0.97  --sat_mode                              false
% 1.52/0.97  --sat_fm_restart_options                ""
% 1.52/0.97  --sat_gr_def                            false
% 1.52/0.97  --sat_epr_types                         true
% 1.52/0.97  --sat_non_cyclic_types                  false
% 1.52/0.97  --sat_finite_models                     false
% 1.52/0.97  --sat_fm_lemmas                         false
% 1.52/0.97  --sat_fm_prep                           false
% 1.52/0.97  --sat_fm_uc_incr                        true
% 1.52/0.97  --sat_out_model                         small
% 1.52/0.97  --sat_out_clauses                       false
% 1.52/0.97  
% 1.52/0.97  ------ QBF Options
% 1.52/0.97  
% 1.52/0.97  --qbf_mode                              false
% 1.52/0.97  --qbf_elim_univ                         false
% 1.52/0.97  --qbf_dom_inst                          none
% 1.52/0.97  --qbf_dom_pre_inst                      false
% 1.52/0.97  --qbf_sk_in                             false
% 1.52/0.97  --qbf_pred_elim                         true
% 1.52/0.97  --qbf_split                             512
% 1.52/0.97  
% 1.52/0.97  ------ BMC1 Options
% 1.52/0.97  
% 1.52/0.97  --bmc1_incremental                      false
% 1.52/0.97  --bmc1_axioms                           reachable_all
% 1.52/0.97  --bmc1_min_bound                        0
% 1.52/0.97  --bmc1_max_bound                        -1
% 1.52/0.97  --bmc1_max_bound_default                -1
% 1.52/0.97  --bmc1_symbol_reachability              true
% 1.52/0.97  --bmc1_property_lemmas                  false
% 1.52/0.97  --bmc1_k_induction                      false
% 1.52/0.97  --bmc1_non_equiv_states                 false
% 1.52/0.97  --bmc1_deadlock                         false
% 1.52/0.97  --bmc1_ucm                              false
% 1.52/0.97  --bmc1_add_unsat_core                   none
% 1.52/0.97  --bmc1_unsat_core_children              false
% 1.52/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.97  --bmc1_out_stat                         full
% 1.52/0.97  --bmc1_ground_init                      false
% 1.52/0.97  --bmc1_pre_inst_next_state              false
% 1.52/0.97  --bmc1_pre_inst_state                   false
% 1.52/0.97  --bmc1_pre_inst_reach_state             false
% 1.52/0.97  --bmc1_out_unsat_core                   false
% 1.52/0.97  --bmc1_aig_witness_out                  false
% 1.52/0.97  --bmc1_verbose                          false
% 1.52/0.97  --bmc1_dump_clauses_tptp                false
% 1.52/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.97  --bmc1_dump_file                        -
% 1.52/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.97  --bmc1_ucm_extend_mode                  1
% 1.52/0.97  --bmc1_ucm_init_mode                    2
% 1.52/0.97  --bmc1_ucm_cone_mode                    none
% 1.52/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.97  --bmc1_ucm_relax_model                  4
% 1.52/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.97  --bmc1_ucm_layered_model                none
% 1.52/0.97  --bmc1_ucm_max_lemma_size               10
% 1.52/0.97  
% 1.52/0.97  ------ AIG Options
% 1.52/0.97  
% 1.52/0.97  --aig_mode                              false
% 1.52/0.97  
% 1.52/0.97  ------ Instantiation Options
% 1.52/0.97  
% 1.52/0.97  --instantiation_flag                    true
% 1.52/0.97  --inst_sos_flag                         false
% 1.52/0.97  --inst_sos_phase                        true
% 1.52/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.97  --inst_lit_sel_side                     none
% 1.52/0.97  --inst_solver_per_active                1400
% 1.52/0.97  --inst_solver_calls_frac                1.
% 1.52/0.97  --inst_passive_queue_type               priority_queues
% 1.52/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.97  --inst_passive_queues_freq              [25;2]
% 1.52/0.97  --inst_dismatching                      true
% 1.52/0.97  --inst_eager_unprocessed_to_passive     true
% 1.52/0.97  --inst_prop_sim_given                   true
% 1.52/0.97  --inst_prop_sim_new                     false
% 1.52/0.97  --inst_subs_new                         false
% 1.52/0.97  --inst_eq_res_simp                      false
% 1.52/0.97  --inst_subs_given                       false
% 1.52/0.97  --inst_orphan_elimination               true
% 1.52/0.97  --inst_learning_loop_flag               true
% 1.52/0.97  --inst_learning_start                   3000
% 1.52/0.97  --inst_learning_factor                  2
% 1.52/0.97  --inst_start_prop_sim_after_learn       3
% 1.52/0.97  --inst_sel_renew                        solver
% 1.52/0.97  --inst_lit_activity_flag                true
% 1.52/0.97  --inst_restr_to_given                   false
% 1.52/0.97  --inst_activity_threshold               500
% 1.52/0.97  --inst_out_proof                        true
% 1.52/0.97  
% 1.52/0.97  ------ Resolution Options
% 1.52/0.97  
% 1.52/0.97  --resolution_flag                       false
% 1.52/0.97  --res_lit_sel                           adaptive
% 1.52/0.97  --res_lit_sel_side                      none
% 1.52/0.97  --res_ordering                          kbo
% 1.52/0.97  --res_to_prop_solver                    active
% 1.52/0.97  --res_prop_simpl_new                    false
% 1.52/0.97  --res_prop_simpl_given                  true
% 1.52/0.97  --res_passive_queue_type                priority_queues
% 1.52/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.97  --res_passive_queues_freq               [15;5]
% 1.52/0.97  --res_forward_subs                      full
% 1.52/0.97  --res_backward_subs                     full
% 1.52/0.97  --res_forward_subs_resolution           true
% 1.52/0.97  --res_backward_subs_resolution          true
% 1.52/0.97  --res_orphan_elimination                true
% 1.52/0.97  --res_time_limit                        2.
% 1.52/0.97  --res_out_proof                         true
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Options
% 1.52/0.97  
% 1.52/0.97  --superposition_flag                    true
% 1.52/0.97  --sup_passive_queue_type                priority_queues
% 1.52/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.97  --demod_completeness_check              fast
% 1.52/0.97  --demod_use_ground                      true
% 1.52/0.97  --sup_to_prop_solver                    passive
% 1.52/0.97  --sup_prop_simpl_new                    true
% 1.52/0.97  --sup_prop_simpl_given                  true
% 1.52/0.97  --sup_fun_splitting                     false
% 1.52/0.97  --sup_smt_interval                      50000
% 1.52/0.97  
% 1.52/0.97  ------ Superposition Simplification Setup
% 1.52/0.97  
% 1.52/0.97  --sup_indices_passive                   []
% 1.52/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_full_bw                           [BwDemod]
% 1.52/0.97  --sup_immed_triv                        [TrivRules]
% 1.52/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_immed_bw_main                     []
% 1.52/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.97  
% 1.52/0.97  ------ Combination Options
% 1.52/0.97  
% 1.52/0.97  --comb_res_mult                         3
% 1.52/0.97  --comb_sup_mult                         2
% 1.52/0.97  --comb_inst_mult                        10
% 1.52/0.97  
% 1.52/0.97  ------ Debug Options
% 1.52/0.97  
% 1.52/0.97  --dbg_backtrace                         false
% 1.52/0.97  --dbg_dump_prop_clauses                 false
% 1.52/0.97  --dbg_dump_prop_clauses_file            -
% 1.52/0.97  --dbg_out_stat                          false
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  ------ Proving...
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  % SZS status Theorem for theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  fof(f13,conjecture,(
% 1.52/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f14,negated_conjecture,(
% 1.52/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.52/0.97    inference(negated_conjecture,[],[f13])).
% 1.52/0.97  
% 1.52/0.97  fof(f18,plain,(
% 1.52/0.97    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.52/0.97    inference(ennf_transformation,[],[f14])).
% 1.52/0.97  
% 1.52/0.97  fof(f19,plain,(
% 1.52/0.97    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.52/0.97    inference(flattening,[],[f18])).
% 1.52/0.97  
% 1.52/0.97  fof(f36,plain,(
% 1.52/0.97    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f37,plain,(
% 1.52/0.97    k1_funct_1(sK7,sK6) != sK5 & r2_hidden(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5)))) & v1_funct_2(sK7,sK4,k1_tarski(sK5)) & v1_funct_1(sK7)),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f19,f36])).
% 1.52/0.97  
% 1.52/0.97  fof(f69,plain,(
% 1.52/0.97    v1_funct_2(sK7,sK4,k1_tarski(sK5))),
% 1.52/0.97    inference(cnf_transformation,[],[f37])).
% 1.52/0.97  
% 1.52/0.97  fof(f3,axiom,(
% 1.52/0.97    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f43,plain,(
% 1.52/0.97    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f3])).
% 1.52/0.97  
% 1.52/0.97  fof(f4,axiom,(
% 1.52/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f44,plain,(
% 1.52/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f4])).
% 1.52/0.97  
% 1.52/0.97  fof(f5,axiom,(
% 1.52/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f45,plain,(
% 1.52/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f5])).
% 1.52/0.97  
% 1.52/0.97  fof(f6,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f46,plain,(
% 1.52/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f6])).
% 1.52/0.97  
% 1.52/0.97  fof(f7,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f47,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f7])).
% 1.52/0.97  
% 1.52/0.97  fof(f8,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f48,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f8])).
% 1.52/0.97  
% 1.52/0.97  fof(f9,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f49,plain,(
% 1.52/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f9])).
% 1.52/0.97  
% 1.52/0.97  fof(f73,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f48,f49])).
% 1.52/0.97  
% 1.52/0.97  fof(f74,plain,(
% 1.52/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f47,f73])).
% 1.52/0.97  
% 1.52/0.97  fof(f75,plain,(
% 1.52/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f46,f74])).
% 1.52/0.97  
% 1.52/0.97  fof(f76,plain,(
% 1.52/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f45,f75])).
% 1.52/0.97  
% 1.52/0.97  fof(f77,plain,(
% 1.52/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f44,f76])).
% 1.52/0.97  
% 1.52/0.97  fof(f78,plain,(
% 1.52/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f43,f77])).
% 1.52/0.97  
% 1.52/0.97  fof(f86,plain,(
% 1.52/0.97    v1_funct_2(sK7,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))),
% 1.52/0.97    inference(definition_unfolding,[],[f69,f78])).
% 1.52/0.97  
% 1.52/0.97  fof(f12,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f16,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.52/0.97    inference(ennf_transformation,[],[f12])).
% 1.52/0.97  
% 1.52/0.97  fof(f17,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.52/0.97    inference(flattening,[],[f16])).
% 1.52/0.97  
% 1.52/0.97  fof(f67,plain,(
% 1.52/0.97    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f17])).
% 1.52/0.97  
% 1.52/0.97  fof(f70,plain,(
% 1.52/0.97    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_tarski(sK5))))),
% 1.52/0.97    inference(cnf_transformation,[],[f37])).
% 1.52/0.97  
% 1.52/0.97  fof(f85,plain,(
% 1.52/0.97    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 1.52/0.97    inference(definition_unfolding,[],[f70,f78])).
% 1.52/0.97  
% 1.52/0.97  fof(f68,plain,(
% 1.52/0.97    v1_funct_1(sK7)),
% 1.52/0.97    inference(cnf_transformation,[],[f37])).
% 1.52/0.97  
% 1.52/0.97  fof(f71,plain,(
% 1.52/0.97    r2_hidden(sK6,sK4)),
% 1.52/0.97    inference(cnf_transformation,[],[f37])).
% 1.52/0.97  
% 1.52/0.97  fof(f72,plain,(
% 1.52/0.97    k1_funct_1(sK7,sK6) != sK5),
% 1.52/0.97    inference(cnf_transformation,[],[f37])).
% 1.52/0.97  
% 1.52/0.97  fof(f2,axiom,(
% 1.52/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f23,plain,(
% 1.52/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.52/0.97    inference(nnf_transformation,[],[f2])).
% 1.52/0.97  
% 1.52/0.97  fof(f24,plain,(
% 1.52/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.52/0.97    inference(rectify,[],[f23])).
% 1.52/0.97  
% 1.52/0.97  fof(f25,plain,(
% 1.52/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f26,plain,(
% 1.52/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 1.52/0.97  
% 1.52/0.97  fof(f39,plain,(
% 1.52/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.52/0.97    inference(cnf_transformation,[],[f26])).
% 1.52/0.97  
% 1.52/0.97  fof(f82,plain,(
% 1.52/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.52/0.97    inference(definition_unfolding,[],[f39,f78])).
% 1.52/0.97  
% 1.52/0.97  fof(f89,plain,(
% 1.52/0.97    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 1.52/0.97    inference(equality_resolution,[],[f82])).
% 1.52/0.97  
% 1.52/0.97  fof(f11,axiom,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f15,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.52/0.97    inference(ennf_transformation,[],[f11])).
% 1.52/0.97  
% 1.52/0.97  fof(f21,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.52/0.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.52/0.97  
% 1.52/0.97  fof(f20,plain,(
% 1.52/0.97    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 1.52/0.97    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.52/0.97  
% 1.52/0.97  fof(f22,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.52/0.97    inference(definition_folding,[],[f15,f21,f20])).
% 1.52/0.97  
% 1.52/0.97  fof(f35,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.52/0.97    inference(nnf_transformation,[],[f22])).
% 1.52/0.97  
% 1.52/0.97  fof(f65,plain,(
% 1.52/0.97    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.52/0.97    inference(cnf_transformation,[],[f35])).
% 1.52/0.97  
% 1.52/0.97  fof(f98,plain,(
% 1.52/0.97    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.52/0.97    inference(equality_resolution,[],[f65])).
% 1.52/0.97  
% 1.52/0.97  fof(f28,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.52/0.97    inference(nnf_transformation,[],[f21])).
% 1.52/0.97  
% 1.52/0.97  fof(f29,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.52/0.97    inference(rectify,[],[f28])).
% 1.52/0.97  
% 1.52/0.97  fof(f30,plain,(
% 1.52/0.97    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.52/0.97    introduced(choice_axiom,[])).
% 1.52/0.97  
% 1.52/0.97  fof(f31,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.52/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.52/0.97  
% 1.52/0.97  fof(f53,plain,(
% 1.52/0.97    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f31])).
% 1.52/0.97  
% 1.52/0.97  fof(f1,axiom,(
% 1.52/0.97    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f38,plain,(
% 1.52/0.97    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.97    inference(cnf_transformation,[],[f1])).
% 1.52/0.97  
% 1.52/0.97  fof(f10,axiom,(
% 1.52/0.97    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 1.52/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.97  
% 1.52/0.97  fof(f27,plain,(
% 1.52/0.97    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 1.52/0.97    inference(nnf_transformation,[],[f10])).
% 1.52/0.97  
% 1.52/0.97  fof(f50,plain,(
% 1.52/0.97    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) )),
% 1.52/0.97    inference(cnf_transformation,[],[f27])).
% 1.52/0.97  
% 1.52/0.97  fof(f84,plain,(
% 1.52/0.97    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.52/0.97    inference(definition_unfolding,[],[f50,f78,f78])).
% 1.52/0.97  
% 1.52/0.97  fof(f32,plain,(
% 1.52/0.97    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.52/0.97    inference(nnf_transformation,[],[f20])).
% 1.52/0.97  
% 1.52/0.97  fof(f33,plain,(
% 1.52/0.97    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.52/0.97    inference(flattening,[],[f32])).
% 1.52/0.97  
% 1.52/0.97  fof(f34,plain,(
% 1.52/0.97    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.52/0.97    inference(rectify,[],[f33])).
% 1.52/0.97  
% 1.52/0.97  fof(f57,plain,(
% 1.52/0.97    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 1.52/0.97    inference(cnf_transformation,[],[f34])).
% 1.52/0.97  
% 1.52/0.97  fof(f97,plain,(
% 1.52/0.97    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.52/0.97    inference(equality_resolution,[],[f57])).
% 1.52/0.97  
% 1.52/0.97  cnf(c_26,negated_conjecture,
% 1.52/0.97      ( v1_funct_2(sK7,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 1.52/0.97      inference(cnf_transformation,[],[f86]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_22,plain,
% 1.52/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 1.52/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.52/0.97      | ~ r2_hidden(X3,X1)
% 1.52/0.97      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.52/0.97      | ~ v1_funct_1(X0)
% 1.52/0.97      | k1_xboole_0 = X2 ),
% 1.52/0.97      inference(cnf_transformation,[],[f67]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_25,negated_conjecture,
% 1.52/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 1.52/0.97      inference(cnf_transformation,[],[f85]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_342,plain,
% 1.52/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 1.52/0.97      | ~ r2_hidden(X3,X1)
% 1.52/0.97      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.52/0.97      | ~ v1_funct_1(X0)
% 1.52/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.52/0.97      | sK7 != X0
% 1.52/0.97      | k1_xboole_0 = X2 ),
% 1.52/0.97      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_343,plain,
% 1.52/0.97      ( ~ v1_funct_2(sK7,X0,X1)
% 1.52/0.97      | ~ r2_hidden(X2,X0)
% 1.52/0.97      | r2_hidden(k1_funct_1(sK7,X2),X1)
% 1.52/0.97      | ~ v1_funct_1(sK7)
% 1.52/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.52/0.97      | k1_xboole_0 = X1 ),
% 1.52/0.97      inference(unflattening,[status(thm)],[c_342]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_27,negated_conjecture,
% 1.52/0.97      ( v1_funct_1(sK7) ),
% 1.52/0.97      inference(cnf_transformation,[],[f68]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_347,plain,
% 1.52/0.97      ( r2_hidden(k1_funct_1(sK7,X2),X1)
% 1.52/0.97      | ~ r2_hidden(X2,X0)
% 1.52/0.97      | ~ v1_funct_2(sK7,X0,X1)
% 1.52/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.52/0.97      | k1_xboole_0 = X1 ),
% 1.52/0.97      inference(global_propositional_subsumption,
% 1.52/0.97                [status(thm)],
% 1.52/0.97                [c_343,c_27]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_348,plain,
% 1.52/0.97      ( ~ v1_funct_2(sK7,X0,X1)
% 1.52/0.97      | ~ r2_hidden(X2,X0)
% 1.52/0.97      | r2_hidden(k1_funct_1(sK7,X2),X1)
% 1.52/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.52/0.97      | k1_xboole_0 = X1 ),
% 1.52/0.97      inference(renaming,[status(thm)],[c_347]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_375,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,X1)
% 1.52/0.97      | r2_hidden(k1_funct_1(sK7,X0),X2)
% 1.52/0.97      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X2
% 1.52/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.52/0.97      | sK4 != X1
% 1.52/0.97      | sK7 != sK7
% 1.52/0.97      | k1_xboole_0 = X2 ),
% 1.52/0.97      inference(resolution_lifted,[status(thm)],[c_26,c_348]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_376,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,sK4)
% 1.52/0.97      | r2_hidden(k1_funct_1(sK7,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 1.52/0.97      | k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k1_zfmisc_1(k2_zfmisc_1(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 1.52/0.97      | k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 1.52/0.97      inference(unflattening,[status(thm)],[c_375]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_960,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,sK4)
% 1.52/0.97      | r2_hidden(k1_funct_1(sK7,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 1.52/0.97      | k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 1.52/0.97      inference(equality_resolution_simp,[status(thm)],[c_376]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2200,plain,
% 1.52/0.97      ( k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 1.52/0.97      | r2_hidden(X0,sK4) != iProver_top
% 1.52/0.97      | r2_hidden(k1_funct_1(sK7,X0),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_960]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_24,negated_conjecture,
% 1.52/0.97      ( r2_hidden(sK6,sK4) ),
% 1.52/0.97      inference(cnf_transformation,[],[f71]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_23,negated_conjecture,
% 1.52/0.97      ( k1_funct_1(sK7,sK6) != sK5 ),
% 1.52/0.97      inference(cnf_transformation,[],[f72]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2374,plain,
% 1.52/0.97      ( r2_hidden(k1_funct_1(sK7,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 1.52/0.97      | ~ r2_hidden(sK6,sK4)
% 1.52/0.97      | k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_960]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_4,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 1.52/0.97      inference(cnf_transformation,[],[f89]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2386,plain,
% 1.52/0.97      ( ~ r2_hidden(k1_funct_1(sK7,sK6),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 1.52/0.97      | k1_funct_1(sK7,sK6) = sK5 ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2414,plain,
% 1.52/0.97      ( k1_xboole_0 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 1.52/0.97      inference(global_propositional_subsumption,
% 1.52/0.97                [status(thm)],
% 1.52/0.97                [c_2200,c_24,c_23,c_2374,c_2386]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_21,plain,
% 1.52/0.97      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 1.52/0.97      inference(cnf_transformation,[],[f98]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2202,plain,
% 1.52/0.97      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2544,plain,
% 1.52/0.97      ( sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,k1_xboole_0) = iProver_top ),
% 1.52/0.97      inference(superposition,[status(thm)],[c_2414,c_2202]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_9,plain,
% 1.52/0.97      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 1.52/0.97      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 1.52/0.97      | r2_hidden(X0,X9) ),
% 1.52/0.97      inference(cnf_transformation,[],[f53]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2464,plain,
% 1.52/0.97      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 1.52/0.97      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,k1_xboole_0)
% 1.52/0.97      | r2_hidden(X0,k1_xboole_0) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2465,plain,
% 1.52/0.97      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 1.52/0.97      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,k1_xboole_0) != iProver_top
% 1.52/0.97      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_2464]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2467,plain,
% 1.52/0.97      ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != iProver_top
% 1.52/0.97      | sP1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,k1_xboole_0) != iProver_top
% 1.52/0.97      | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_2465]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_0,plain,
% 1.52/0.97      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.52/0.97      inference(cnf_transformation,[],[f38]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2395,plain,
% 1.52/0.97      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2400,plain,
% 1.52/0.97      ( k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_xboole_0) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_2395]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_6,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,X1)
% 1.52/0.97      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 1.52/0.97      inference(cnf_transformation,[],[f84]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2394,plain,
% 1.52/0.97      ( ~ r2_hidden(X0,k1_xboole_0)
% 1.52/0.97      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2396,plain,
% 1.52/0.97      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 1.52/0.97      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_2394]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_2398,plain,
% 1.52/0.97      ( k4_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_xboole_0) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 1.52/0.97      | r2_hidden(sK5,k1_xboole_0) != iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_2396]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_18,plain,
% 1.52/0.97      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 1.52/0.97      inference(cnf_transformation,[],[f97]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_44,plain,
% 1.52/0.97      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) = iProver_top ),
% 1.52/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(c_46,plain,
% 1.52/0.97      ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = iProver_top ),
% 1.52/0.97      inference(instantiation,[status(thm)],[c_44]) ).
% 1.52/0.97  
% 1.52/0.97  cnf(contradiction,plain,
% 1.52/0.97      ( $false ),
% 1.52/0.97      inference(minisat,[status(thm)],[c_2544,c_2467,c_2400,c_2398,c_46]) ).
% 1.52/0.97  
% 1.52/0.97  
% 1.52/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.52/0.97  
% 1.52/0.97  ------                               Statistics
% 1.52/0.97  
% 1.52/0.97  ------ General
% 1.52/0.97  
% 1.52/0.97  abstr_ref_over_cycles:                  0
% 1.52/0.97  abstr_ref_under_cycles:                 0
% 1.52/0.97  gc_basic_clause_elim:                   0
% 1.52/0.97  forced_gc_time:                         0
% 1.52/0.97  parsing_time:                           0.009
% 1.52/0.97  unif_index_cands_time:                  0.
% 1.52/0.97  unif_index_add_time:                    0.
% 1.52/0.97  orderings_time:                         0.
% 1.52/0.97  out_proof_time:                         0.009
% 1.52/0.97  total_time:                             0.097
% 1.52/0.97  num_of_symbols:                         49
% 1.52/0.97  num_of_terms:                           1558
% 1.52/0.97  
% 1.52/0.97  ------ Preprocessing
% 1.52/0.97  
% 1.52/0.97  num_of_splits:                          0
% 1.52/0.97  num_of_split_atoms:                     0
% 1.52/0.97  num_of_reused_defs:                     0
% 1.52/0.97  num_eq_ax_congr_red:                    81
% 1.52/0.97  num_of_sem_filtered_clauses:            1
% 1.52/0.97  num_of_subtypes:                        0
% 1.52/0.97  monotx_restored_types:                  0
% 1.52/0.97  sat_num_of_epr_types:                   0
% 1.52/0.97  sat_num_of_non_cyclic_types:            0
% 1.52/0.97  sat_guarded_non_collapsed_types:        0
% 1.52/0.97  num_pure_diseq_elim:                    0
% 1.52/0.97  simp_replaced_by:                       0
% 1.52/0.97  res_preprocessed:                       120
% 1.52/0.97  prep_upred:                             0
% 1.52/0.97  prep_unflattend:                        599
% 1.52/0.97  smt_new_axioms:                         0
% 1.52/0.97  pred_elim_cands:                        3
% 1.52/0.97  pred_elim:                              3
% 1.52/0.97  pred_elim_cl:                           3
% 1.52/0.97  pred_elim_cycles:                       7
% 1.52/0.97  merged_defs:                            8
% 1.52/0.97  merged_defs_ncl:                        0
% 1.52/0.97  bin_hyper_res:                          8
% 1.52/0.97  prep_cycles:                            4
% 1.52/0.97  pred_elim_time:                         0.024
% 1.52/0.97  splitting_time:                         0.
% 1.52/0.97  sem_filter_time:                        0.
% 1.52/0.97  monotx_time:                            0.001
% 1.52/0.97  subtype_inf_time:                       0.
% 1.52/0.97  
% 1.52/0.97  ------ Problem properties
% 1.52/0.97  
% 1.52/0.97  clauses:                                25
% 1.52/0.97  conjectures:                            2
% 1.52/0.97  epr:                                    12
% 1.52/0.97  horn:                                   20
% 1.52/0.97  ground:                                 2
% 1.52/0.97  unary:                                  13
% 1.52/0.97  binary:                                 4
% 1.52/0.97  lits:                                   51
% 1.52/0.97  lits_eq:                                19
% 1.52/0.97  fd_pure:                                0
% 1.52/0.97  fd_pseudo:                              0
% 1.52/0.97  fd_cond:                                0
% 1.52/0.97  fd_pseudo_cond:                         4
% 1.52/0.97  ac_symbols:                             0
% 1.52/0.97  
% 1.52/0.97  ------ Propositional Solver
% 1.52/0.97  
% 1.52/0.97  prop_solver_calls:                      24
% 1.52/0.97  prop_fast_solver_calls:                 761
% 1.52/0.97  smt_solver_calls:                       0
% 1.52/0.97  smt_fast_solver_calls:                  0
% 1.52/0.97  prop_num_of_clauses:                    294
% 1.52/0.97  prop_preprocess_simplified:             3799
% 1.52/0.97  prop_fo_subsumed:                       3
% 1.52/0.97  prop_solver_time:                       0.
% 1.52/0.97  smt_solver_time:                        0.
% 1.52/0.97  smt_fast_solver_time:                   0.
% 1.52/0.97  prop_fast_solver_time:                  0.
% 1.52/0.97  prop_unsat_core_time:                   0.
% 1.52/0.97  
% 1.52/0.97  ------ QBF
% 1.52/0.97  
% 1.52/0.97  qbf_q_res:                              0
% 1.52/0.97  qbf_num_tautologies:                    0
% 1.52/0.97  qbf_prep_cycles:                        0
% 1.52/0.97  
% 1.52/0.97  ------ BMC1
% 1.52/0.97  
% 1.52/0.97  bmc1_current_bound:                     -1
% 1.52/0.97  bmc1_last_solved_bound:                 -1
% 1.52/0.97  bmc1_unsat_core_size:                   -1
% 1.52/0.97  bmc1_unsat_core_parents_size:           -1
% 1.52/0.97  bmc1_merge_next_fun:                    0
% 1.52/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.52/0.97  
% 1.52/0.97  ------ Instantiation
% 1.52/0.97  
% 1.52/0.97  inst_num_of_clauses:                    74
% 1.52/0.97  inst_num_in_passive:                    24
% 1.52/0.97  inst_num_in_active:                     46
% 1.52/0.97  inst_num_in_unprocessed:                4
% 1.52/0.97  inst_num_of_loops:                      50
% 1.52/0.97  inst_num_of_learning_restarts:          0
% 1.52/0.97  inst_num_moves_active_passive:          3
% 1.52/0.97  inst_lit_activity:                      0
% 1.52/0.97  inst_lit_activity_moves:                0
% 1.52/0.97  inst_num_tautologies:                   0
% 1.52/0.97  inst_num_prop_implied:                  0
% 1.52/0.97  inst_num_existing_simplified:           0
% 1.52/0.97  inst_num_eq_res_simplified:             0
% 1.52/0.97  inst_num_child_elim:                    0
% 1.52/0.97  inst_num_of_dismatching_blockings:      0
% 1.52/0.97  inst_num_of_non_proper_insts:           32
% 1.52/0.97  inst_num_of_duplicates:                 0
% 1.52/0.97  inst_inst_num_from_inst_to_res:         0
% 1.52/0.97  inst_dismatching_checking_time:         0.
% 1.52/0.97  
% 1.52/0.97  ------ Resolution
% 1.52/0.97  
% 1.52/0.97  res_num_of_clauses:                     0
% 1.52/0.97  res_num_in_passive:                     0
% 1.52/0.97  res_num_in_active:                      0
% 1.52/0.97  res_num_of_loops:                       124
% 1.52/0.97  res_forward_subset_subsumed:            3
% 1.52/0.97  res_backward_subset_subsumed:           0
% 1.52/0.97  res_forward_subsumed:                   0
% 1.52/0.97  res_backward_subsumed:                  0
% 1.52/0.97  res_forward_subsumption_resolution:     0
% 1.52/0.97  res_backward_subsumption_resolution:    0
% 1.52/0.98  res_clause_to_clause_subsumption:       678
% 1.52/0.98  res_orphan_elimination:                 0
% 1.52/0.98  res_tautology_del:                      37
% 1.52/0.98  res_num_eq_res_simplified:              1
% 1.52/0.98  res_num_sel_changes:                    0
% 1.52/0.98  res_moves_from_active_to_pass:          0
% 1.52/0.98  
% 1.52/0.98  ------ Superposition
% 1.52/0.98  
% 1.52/0.98  sup_time_total:                         0.
% 1.52/0.98  sup_time_generating:                    0.
% 1.52/0.98  sup_time_sim_full:                      0.
% 1.52/0.98  sup_time_sim_immed:                     0.
% 1.52/0.98  
% 1.52/0.98  sup_num_of_clauses:                     26
% 1.52/0.98  sup_num_in_active:                      9
% 1.52/0.98  sup_num_in_passive:                     17
% 1.52/0.98  sup_num_of_loops:                       8
% 1.52/0.98  sup_fw_superposition:                   1
% 1.52/0.98  sup_bw_superposition:                   0
% 1.52/0.98  sup_immediate_simplified:               0
% 1.52/0.98  sup_given_eliminated:                   0
% 1.52/0.98  comparisons_done:                       0
% 1.52/0.98  comparisons_avoided:                    0
% 1.52/0.98  
% 1.52/0.98  ------ Simplifications
% 1.52/0.98  
% 1.52/0.98  
% 1.52/0.98  sim_fw_subset_subsumed:                 0
% 1.52/0.98  sim_bw_subset_subsumed:                 0
% 1.52/0.98  sim_fw_subsumed:                        0
% 1.52/0.98  sim_bw_subsumed:                        0
% 1.52/0.98  sim_fw_subsumption_res:                 0
% 1.52/0.98  sim_bw_subsumption_res:                 0
% 1.52/0.98  sim_tautology_del:                      0
% 1.52/0.98  sim_eq_tautology_del:                   0
% 1.52/0.98  sim_eq_res_simp:                        0
% 1.52/0.98  sim_fw_demodulated:                     0
% 1.52/0.98  sim_bw_demodulated:                     0
% 1.52/0.98  sim_light_normalised:                   0
% 1.52/0.98  sim_joinable_taut:                      0
% 1.52/0.98  sim_joinable_simp:                      0
% 1.52/0.98  sim_ac_normalised:                      0
% 1.52/0.98  sim_smt_subsumption:                    0
% 1.52/0.98  
%------------------------------------------------------------------------------
