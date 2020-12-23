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
% DateTime   : Thu Dec  3 11:57:56 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 722 expanded)
%              Number of clauses        :   38 (  59 expanded)
%              Number of leaves         :   24 ( 229 expanded)
%              Depth                    :   16
%              Number of atoms          :  351 (1226 expanded)
%              Number of equality atoms :  281 (1087 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK3,sK4) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK2) = sK2
        | k1_mcart_1(sK2) = sK2 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK2 ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k2_mcart_1(sK2) = sK2
      | k1_mcart_1(sK2) = sK2 )
    & k4_tarski(sK3,sK4) = sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f37,f36])).

fof(f78,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f19])).

fof(f16,axiom,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f82])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f83])).

fof(f95,plain,(
    ! [X0,X1] : k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f57,f87,f87,f87])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f26,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f31,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7
                & X5 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | X5 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X0 != X7
              & X1 != X7
              & X2 != X7
              & X3 != X7
              & X4 != X7
              & X5 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X0 = X7
            | X1 = X7
            | X2 = X7
            | X3 = X7
            | X4 = X7
            | X5 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6) != X0
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X5 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK1(X0,X1,X2,X3,X4,X5,X6) = X0
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X5
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6) != X0
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X5 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK1(X0,X1,X2,X3,X4,X5,X6) = X0
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X5
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f104,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X0,X1,X2,X3,X4,X8,X6) ) ),
    inference(equality_resolution,[],[f59])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP0(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f24,f26])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f97])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f83])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f84])).

fof(f94,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f55,f85,f87,f87,f87])).

fof(f98,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f94])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f84])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f83])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f42,f85,f86])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f89,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f41,f84,f86])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f87])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_28,negated_conjecture,
    ( k1_mcart_1(sK2) = sK2
    | k2_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,negated_conjecture,
    ( k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_27,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3431,plain,
    ( k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_29,c_27])).

cnf(c_3442,plain,
    ( k2_mcart_1(sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_28,c_3431])).

cnf(c_26,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3428,plain,
    ( k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_29,c_26])).

cnf(c_3444,plain,
    ( sK4 = sK2
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_3442,c_3428])).

cnf(c_3447,plain,
    ( k4_tarski(sK3,sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_3444,c_29])).

cnf(c_9,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3660,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_3447,c_9])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3235,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3966,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK3 = sK2
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3660,c_3235])).

cnf(c_22,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X5,X6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_25,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1285,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | X11 != X12
    | k6_enumset1(X4,X4,X4,X5,X7,X9,X11,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_25])).

cnf(c_1286,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(unflattening,[status(thm)],[c_1285])).

cnf(c_1287,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1286])).

cnf(c_1289,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_8,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3298,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_1])).

cnf(c_3371,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8,c_0,c_3298])).

cnf(c_3391,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3371])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3552,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3556,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3552])).

cnf(c_3558,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3556])).

cnf(c_4062,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3966,c_1289,c_3391,c_3558])).

cnf(c_3659,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_29,c_9])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3234,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3815,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3659,c_3234])).

cnf(c_4065,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4062,c_3815])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4065,c_3558,c_3391,c_1289])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n018.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:58:41 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.67/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/0.92  
% 2.67/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.92  
% 2.67/0.92  ------  iProver source info
% 2.67/0.92  
% 2.67/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.92  git: non_committed_changes: false
% 2.67/0.92  git: last_make_outside_of_git: false
% 2.67/0.92  
% 2.67/0.92  ------ 
% 2.67/0.92  
% 2.67/0.92  ------ Input Options
% 2.67/0.92  
% 2.67/0.92  --out_options                           all
% 2.67/0.92  --tptp_safe_out                         true
% 2.67/0.92  --problem_path                          ""
% 2.67/0.92  --include_path                          ""
% 2.67/0.92  --clausifier                            res/vclausify_rel
% 2.67/0.92  --clausifier_options                    --mode clausify
% 2.67/0.92  --stdin                                 false
% 2.67/0.92  --stats_out                             all
% 2.67/0.92  
% 2.67/0.92  ------ General Options
% 2.67/0.92  
% 2.67/0.92  --fof                                   false
% 2.67/0.92  --time_out_real                         305.
% 2.67/0.92  --time_out_virtual                      -1.
% 2.67/0.92  --symbol_type_check                     false
% 2.67/0.92  --clausify_out                          false
% 2.67/0.92  --sig_cnt_out                           false
% 2.67/0.92  --trig_cnt_out                          false
% 2.67/0.92  --trig_cnt_out_tolerance                1.
% 2.67/0.92  --trig_cnt_out_sk_spl                   false
% 2.67/0.92  --abstr_cl_out                          false
% 2.67/0.92  
% 2.67/0.92  ------ Global Options
% 2.67/0.92  
% 2.67/0.92  --schedule                              default
% 2.67/0.92  --add_important_lit                     false
% 2.67/0.92  --prop_solver_per_cl                    1000
% 2.67/0.92  --min_unsat_core                        false
% 2.67/0.92  --soft_assumptions                      false
% 2.67/0.92  --soft_lemma_size                       3
% 2.67/0.92  --prop_impl_unit_size                   0
% 2.67/0.92  --prop_impl_unit                        []
% 2.67/0.92  --share_sel_clauses                     true
% 2.67/0.92  --reset_solvers                         false
% 2.67/0.92  --bc_imp_inh                            [conj_cone]
% 2.67/0.92  --conj_cone_tolerance                   3.
% 2.67/0.92  --extra_neg_conj                        none
% 2.67/0.92  --large_theory_mode                     true
% 2.67/0.92  --prolific_symb_bound                   200
% 2.67/0.92  --lt_threshold                          2000
% 2.67/0.92  --clause_weak_htbl                      true
% 2.67/0.92  --gc_record_bc_elim                     false
% 2.67/0.92  
% 2.67/0.92  ------ Preprocessing Options
% 2.67/0.92  
% 2.67/0.92  --preprocessing_flag                    true
% 2.67/0.92  --time_out_prep_mult                    0.1
% 2.67/0.92  --splitting_mode                        input
% 2.67/0.92  --splitting_grd                         true
% 2.67/0.92  --splitting_cvd                         false
% 2.67/0.92  --splitting_cvd_svl                     false
% 2.67/0.92  --splitting_nvd                         32
% 2.67/0.92  --sub_typing                            true
% 2.67/0.92  --prep_gs_sim                           true
% 2.67/0.92  --prep_unflatten                        true
% 2.67/0.92  --prep_res_sim                          true
% 2.67/0.92  --prep_upred                            true
% 2.67/0.92  --prep_sem_filter                       exhaustive
% 2.67/0.92  --prep_sem_filter_out                   false
% 2.67/0.92  --pred_elim                             true
% 2.67/0.92  --res_sim_input                         true
% 2.67/0.92  --eq_ax_congr_red                       true
% 2.67/0.92  --pure_diseq_elim                       true
% 2.67/0.92  --brand_transform                       false
% 2.67/0.92  --non_eq_to_eq                          false
% 2.67/0.92  --prep_def_merge                        true
% 2.67/0.92  --prep_def_merge_prop_impl              false
% 2.67/0.92  --prep_def_merge_mbd                    true
% 2.67/0.92  --prep_def_merge_tr_red                 false
% 2.67/0.92  --prep_def_merge_tr_cl                  false
% 2.67/0.92  --smt_preprocessing                     true
% 2.67/0.92  --smt_ac_axioms                         fast
% 2.67/0.92  --preprocessed_out                      false
% 2.67/0.92  --preprocessed_stats                    false
% 2.67/0.92  
% 2.67/0.92  ------ Abstraction refinement Options
% 2.67/0.92  
% 2.67/0.92  --abstr_ref                             []
% 2.67/0.92  --abstr_ref_prep                        false
% 2.67/0.92  --abstr_ref_until_sat                   false
% 2.67/0.92  --abstr_ref_sig_restrict                funpre
% 2.67/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.92  --abstr_ref_under                       []
% 2.67/0.92  
% 2.67/0.92  ------ SAT Options
% 2.67/0.92  
% 2.67/0.92  --sat_mode                              false
% 2.67/0.92  --sat_fm_restart_options                ""
% 2.67/0.92  --sat_gr_def                            false
% 2.67/0.92  --sat_epr_types                         true
% 2.67/0.92  --sat_non_cyclic_types                  false
% 2.67/0.92  --sat_finite_models                     false
% 2.67/0.92  --sat_fm_lemmas                         false
% 2.67/0.92  --sat_fm_prep                           false
% 2.67/0.92  --sat_fm_uc_incr                        true
% 2.67/0.92  --sat_out_model                         small
% 2.67/0.92  --sat_out_clauses                       false
% 2.67/0.92  
% 2.67/0.92  ------ QBF Options
% 2.67/0.92  
% 2.67/0.92  --qbf_mode                              false
% 2.67/0.92  --qbf_elim_univ                         false
% 2.67/0.92  --qbf_dom_inst                          none
% 2.67/0.92  --qbf_dom_pre_inst                      false
% 2.67/0.92  --qbf_sk_in                             false
% 2.67/0.92  --qbf_pred_elim                         true
% 2.67/0.92  --qbf_split                             512
% 2.67/0.92  
% 2.67/0.92  ------ BMC1 Options
% 2.67/0.92  
% 2.67/0.92  --bmc1_incremental                      false
% 2.67/0.92  --bmc1_axioms                           reachable_all
% 2.67/0.92  --bmc1_min_bound                        0
% 2.67/0.92  --bmc1_max_bound                        -1
% 2.67/0.92  --bmc1_max_bound_default                -1
% 2.67/0.92  --bmc1_symbol_reachability              true
% 2.67/0.92  --bmc1_property_lemmas                  false
% 2.67/0.92  --bmc1_k_induction                      false
% 2.67/0.92  --bmc1_non_equiv_states                 false
% 2.67/0.92  --bmc1_deadlock                         false
% 2.67/0.92  --bmc1_ucm                              false
% 2.67/0.92  --bmc1_add_unsat_core                   none
% 2.67/0.92  --bmc1_unsat_core_children              false
% 2.67/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.92  --bmc1_out_stat                         full
% 2.67/0.92  --bmc1_ground_init                      false
% 2.67/0.92  --bmc1_pre_inst_next_state              false
% 2.67/0.92  --bmc1_pre_inst_state                   false
% 2.67/0.92  --bmc1_pre_inst_reach_state             false
% 2.67/0.92  --bmc1_out_unsat_core                   false
% 2.67/0.92  --bmc1_aig_witness_out                  false
% 2.67/0.92  --bmc1_verbose                          false
% 2.67/0.92  --bmc1_dump_clauses_tptp                false
% 2.67/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.92  --bmc1_dump_file                        -
% 2.67/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.92  --bmc1_ucm_extend_mode                  1
% 2.67/0.92  --bmc1_ucm_init_mode                    2
% 2.67/0.92  --bmc1_ucm_cone_mode                    none
% 2.67/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.92  --bmc1_ucm_relax_model                  4
% 2.67/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.92  --bmc1_ucm_layered_model                none
% 2.67/0.92  --bmc1_ucm_max_lemma_size               10
% 2.67/0.92  
% 2.67/0.92  ------ AIG Options
% 2.67/0.92  
% 2.67/0.92  --aig_mode                              false
% 2.67/0.92  
% 2.67/0.92  ------ Instantiation Options
% 2.67/0.92  
% 2.67/0.92  --instantiation_flag                    true
% 2.67/0.92  --inst_sos_flag                         false
% 2.67/0.92  --inst_sos_phase                        true
% 2.67/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.92  --inst_lit_sel_side                     num_symb
% 2.67/0.92  --inst_solver_per_active                1400
% 2.67/0.92  --inst_solver_calls_frac                1.
% 2.67/0.92  --inst_passive_queue_type               priority_queues
% 2.67/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.92  --inst_passive_queues_freq              [25;2]
% 2.67/0.92  --inst_dismatching                      true
% 2.67/0.92  --inst_eager_unprocessed_to_passive     true
% 2.67/0.92  --inst_prop_sim_given                   true
% 2.67/0.92  --inst_prop_sim_new                     false
% 2.67/0.92  --inst_subs_new                         false
% 2.67/0.92  --inst_eq_res_simp                      false
% 2.67/0.92  --inst_subs_given                       false
% 2.67/0.92  --inst_orphan_elimination               true
% 2.67/0.92  --inst_learning_loop_flag               true
% 2.67/0.92  --inst_learning_start                   3000
% 2.67/0.92  --inst_learning_factor                  2
% 2.67/0.92  --inst_start_prop_sim_after_learn       3
% 2.67/0.92  --inst_sel_renew                        solver
% 2.67/0.92  --inst_lit_activity_flag                true
% 2.67/0.92  --inst_restr_to_given                   false
% 2.67/0.92  --inst_activity_threshold               500
% 2.67/0.92  --inst_out_proof                        true
% 2.67/0.92  
% 2.67/0.92  ------ Resolution Options
% 2.67/0.92  
% 2.67/0.92  --resolution_flag                       true
% 2.67/0.92  --res_lit_sel                           adaptive
% 2.67/0.92  --res_lit_sel_side                      none
% 2.67/0.92  --res_ordering                          kbo
% 2.67/0.92  --res_to_prop_solver                    active
% 2.67/0.92  --res_prop_simpl_new                    false
% 2.67/0.92  --res_prop_simpl_given                  true
% 2.67/0.92  --res_passive_queue_type                priority_queues
% 2.67/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.92  --res_passive_queues_freq               [15;5]
% 2.67/0.92  --res_forward_subs                      full
% 2.67/0.92  --res_backward_subs                     full
% 2.67/0.92  --res_forward_subs_resolution           true
% 2.67/0.92  --res_backward_subs_resolution          true
% 2.67/0.92  --res_orphan_elimination                true
% 2.67/0.92  --res_time_limit                        2.
% 2.67/0.92  --res_out_proof                         true
% 2.67/0.92  
% 2.67/0.92  ------ Superposition Options
% 2.67/0.92  
% 2.67/0.92  --superposition_flag                    true
% 2.67/0.92  --sup_passive_queue_type                priority_queues
% 2.67/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.92  --demod_completeness_check              fast
% 2.67/0.92  --demod_use_ground                      true
% 2.67/0.92  --sup_to_prop_solver                    passive
% 2.67/0.92  --sup_prop_simpl_new                    true
% 2.67/0.92  --sup_prop_simpl_given                  true
% 2.67/0.92  --sup_fun_splitting                     false
% 2.67/0.92  --sup_smt_interval                      50000
% 2.67/0.92  
% 2.67/0.92  ------ Superposition Simplification Setup
% 2.67/0.92  
% 2.67/0.92  --sup_indices_passive                   []
% 2.67/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.92  --sup_full_bw                           [BwDemod]
% 2.67/0.92  --sup_immed_triv                        [TrivRules]
% 2.67/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.92  --sup_immed_bw_main                     []
% 2.67/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.92  
% 2.67/0.92  ------ Combination Options
% 2.67/0.92  
% 2.67/0.92  --comb_res_mult                         3
% 2.67/0.92  --comb_sup_mult                         2
% 2.67/0.92  --comb_inst_mult                        10
% 2.67/0.92  
% 2.67/0.92  ------ Debug Options
% 2.67/0.92  
% 2.67/0.92  --dbg_backtrace                         false
% 2.67/0.92  --dbg_dump_prop_clauses                 false
% 2.67/0.92  --dbg_dump_prop_clauses_file            -
% 2.67/0.92  --dbg_out_stat                          false
% 2.67/0.92  ------ Parsing...
% 2.67/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/0.92  
% 2.67/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.67/0.92  
% 2.67/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/0.92  
% 2.67/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/0.92  ------ Proving...
% 2.67/0.92  ------ Problem Properties 
% 2.67/0.92  
% 2.67/0.92  
% 2.67/0.92  clauses                                 30
% 2.67/0.92  conjectures                             2
% 2.67/0.92  EPR                                     7
% 2.67/0.92  Horn                                    26
% 2.67/0.92  unary                                   9
% 2.67/0.92  binary                                  13
% 2.67/0.92  lits                                    69
% 2.67/0.92  lits eq                                 33
% 2.67/0.92  fd_pure                                 0
% 2.67/0.92  fd_pseudo                               0
% 2.67/0.92  fd_cond                                 2
% 2.67/0.92  fd_pseudo_cond                          3
% 2.67/0.92  AC symbols                              0
% 2.67/0.92  
% 2.67/0.92  ------ Schedule dynamic 5 is on 
% 2.67/0.92  
% 2.67/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/0.92  
% 2.67/0.92  
% 2.67/0.92  ------ 
% 2.67/0.92  Current options:
% 2.67/0.92  ------ 
% 2.67/0.92  
% 2.67/0.92  ------ Input Options
% 2.67/0.92  
% 2.67/0.92  --out_options                           all
% 2.67/0.92  --tptp_safe_out                         true
% 2.67/0.92  --problem_path                          ""
% 2.67/0.92  --include_path                          ""
% 2.67/0.92  --clausifier                            res/vclausify_rel
% 2.67/0.92  --clausifier_options                    --mode clausify
% 2.67/0.92  --stdin                                 false
% 2.67/0.92  --stats_out                             all
% 2.67/0.92  
% 2.67/0.92  ------ General Options
% 2.67/0.92  
% 2.67/0.92  --fof                                   false
% 2.67/0.92  --time_out_real                         305.
% 2.67/0.92  --time_out_virtual                      -1.
% 2.67/0.92  --symbol_type_check                     false
% 2.67/0.92  --clausify_out                          false
% 2.67/0.92  --sig_cnt_out                           false
% 2.67/0.92  --trig_cnt_out                          false
% 2.67/0.92  --trig_cnt_out_tolerance                1.
% 2.67/0.92  --trig_cnt_out_sk_spl                   false
% 2.67/0.92  --abstr_cl_out                          false
% 2.67/0.92  
% 2.67/0.92  ------ Global Options
% 2.67/0.92  
% 2.67/0.92  --schedule                              default
% 2.67/0.92  --add_important_lit                     false
% 2.67/0.92  --prop_solver_per_cl                    1000
% 2.67/0.92  --min_unsat_core                        false
% 2.67/0.92  --soft_assumptions                      false
% 2.67/0.92  --soft_lemma_size                       3
% 2.67/0.92  --prop_impl_unit_size                   0
% 2.67/0.92  --prop_impl_unit                        []
% 2.67/0.92  --share_sel_clauses                     true
% 2.67/0.92  --reset_solvers                         false
% 2.67/0.92  --bc_imp_inh                            [conj_cone]
% 2.67/0.92  --conj_cone_tolerance                   3.
% 2.67/0.92  --extra_neg_conj                        none
% 2.67/0.92  --large_theory_mode                     true
% 2.67/0.92  --prolific_symb_bound                   200
% 2.67/0.92  --lt_threshold                          2000
% 2.67/0.92  --clause_weak_htbl                      true
% 2.67/0.92  --gc_record_bc_elim                     false
% 2.67/0.92  
% 2.67/0.92  ------ Preprocessing Options
% 2.67/0.92  
% 2.67/0.92  --preprocessing_flag                    true
% 2.67/0.92  --time_out_prep_mult                    0.1
% 2.67/0.92  --splitting_mode                        input
% 2.67/0.92  --splitting_grd                         true
% 2.67/0.92  --splitting_cvd                         false
% 2.67/0.92  --splitting_cvd_svl                     false
% 2.67/0.92  --splitting_nvd                         32
% 2.67/0.92  --sub_typing                            true
% 2.67/0.92  --prep_gs_sim                           true
% 2.67/0.92  --prep_unflatten                        true
% 2.67/0.92  --prep_res_sim                          true
% 2.67/0.92  --prep_upred                            true
% 2.67/0.92  --prep_sem_filter                       exhaustive
% 2.67/0.92  --prep_sem_filter_out                   false
% 2.67/0.92  --pred_elim                             true
% 2.67/0.92  --res_sim_input                         true
% 2.67/0.92  --eq_ax_congr_red                       true
% 2.67/0.92  --pure_diseq_elim                       true
% 2.67/0.92  --brand_transform                       false
% 2.67/0.92  --non_eq_to_eq                          false
% 2.67/0.92  --prep_def_merge                        true
% 2.67/0.92  --prep_def_merge_prop_impl              false
% 2.67/0.92  --prep_def_merge_mbd                    true
% 2.67/0.92  --prep_def_merge_tr_red                 false
% 2.67/0.92  --prep_def_merge_tr_cl                  false
% 2.67/0.92  --smt_preprocessing                     true
% 2.67/0.92  --smt_ac_axioms                         fast
% 2.67/0.92  --preprocessed_out                      false
% 2.67/0.92  --preprocessed_stats                    false
% 2.67/0.92  
% 2.67/0.92  ------ Abstraction refinement Options
% 2.67/0.92  
% 2.67/0.92  --abstr_ref                             []
% 2.67/0.92  --abstr_ref_prep                        false
% 2.67/0.92  --abstr_ref_until_sat                   false
% 2.67/0.92  --abstr_ref_sig_restrict                funpre
% 2.67/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.92  --abstr_ref_under                       []
% 2.67/0.92  
% 2.67/0.92  ------ SAT Options
% 2.67/0.92  
% 2.67/0.92  --sat_mode                              false
% 2.67/0.92  --sat_fm_restart_options                ""
% 2.67/0.92  --sat_gr_def                            false
% 2.67/0.92  --sat_epr_types                         true
% 2.67/0.92  --sat_non_cyclic_types                  false
% 2.67/0.92  --sat_finite_models                     false
% 2.67/0.92  --sat_fm_lemmas                         false
% 2.67/0.92  --sat_fm_prep                           false
% 2.67/0.92  --sat_fm_uc_incr                        true
% 2.67/0.92  --sat_out_model                         small
% 2.67/0.92  --sat_out_clauses                       false
% 2.67/0.92  
% 2.67/0.92  ------ QBF Options
% 2.67/0.92  
% 2.67/0.92  --qbf_mode                              false
% 2.67/0.92  --qbf_elim_univ                         false
% 2.67/0.92  --qbf_dom_inst                          none
% 2.67/0.92  --qbf_dom_pre_inst                      false
% 2.67/0.92  --qbf_sk_in                             false
% 2.67/0.92  --qbf_pred_elim                         true
% 2.67/0.92  --qbf_split                             512
% 2.67/0.92  
% 2.67/0.92  ------ BMC1 Options
% 2.67/0.92  
% 2.67/0.92  --bmc1_incremental                      false
% 2.67/0.92  --bmc1_axioms                           reachable_all
% 2.67/0.92  --bmc1_min_bound                        0
% 2.67/0.92  --bmc1_max_bound                        -1
% 2.67/0.92  --bmc1_max_bound_default                -1
% 2.67/0.92  --bmc1_symbol_reachability              true
% 2.67/0.92  --bmc1_property_lemmas                  false
% 2.67/0.92  --bmc1_k_induction                      false
% 2.67/0.92  --bmc1_non_equiv_states                 false
% 2.67/0.92  --bmc1_deadlock                         false
% 2.67/0.92  --bmc1_ucm                              false
% 2.67/0.92  --bmc1_add_unsat_core                   none
% 2.67/0.92  --bmc1_unsat_core_children              false
% 2.67/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.92  --bmc1_out_stat                         full
% 2.67/0.92  --bmc1_ground_init                      false
% 2.67/0.92  --bmc1_pre_inst_next_state              false
% 2.67/0.92  --bmc1_pre_inst_state                   false
% 2.67/0.92  --bmc1_pre_inst_reach_state             false
% 2.67/0.92  --bmc1_out_unsat_core                   false
% 2.67/0.92  --bmc1_aig_witness_out                  false
% 2.67/0.92  --bmc1_verbose                          false
% 2.67/0.92  --bmc1_dump_clauses_tptp                false
% 2.67/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.92  --bmc1_dump_file                        -
% 2.67/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.92  --bmc1_ucm_extend_mode                  1
% 2.67/0.92  --bmc1_ucm_init_mode                    2
% 2.67/0.92  --bmc1_ucm_cone_mode                    none
% 2.67/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.92  --bmc1_ucm_relax_model                  4
% 2.67/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.92  --bmc1_ucm_layered_model                none
% 2.67/0.92  --bmc1_ucm_max_lemma_size               10
% 2.67/0.92  
% 2.67/0.92  ------ AIG Options
% 2.67/0.92  
% 2.67/0.92  --aig_mode                              false
% 2.67/0.92  
% 2.67/0.92  ------ Instantiation Options
% 2.67/0.92  
% 2.67/0.92  --instantiation_flag                    true
% 2.67/0.92  --inst_sos_flag                         false
% 2.67/0.92  --inst_sos_phase                        true
% 2.67/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.92  --inst_lit_sel_side                     none
% 2.67/0.92  --inst_solver_per_active                1400
% 2.67/0.92  --inst_solver_calls_frac                1.
% 2.67/0.92  --inst_passive_queue_type               priority_queues
% 2.67/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.92  --inst_passive_queues_freq              [25;2]
% 2.67/0.92  --inst_dismatching                      true
% 2.67/0.92  --inst_eager_unprocessed_to_passive     true
% 2.67/0.92  --inst_prop_sim_given                   true
% 2.67/0.92  --inst_prop_sim_new                     false
% 2.67/0.92  --inst_subs_new                         false
% 2.67/0.92  --inst_eq_res_simp                      false
% 2.67/0.92  --inst_subs_given                       false
% 2.67/0.92  --inst_orphan_elimination               true
% 2.67/0.92  --inst_learning_loop_flag               true
% 2.67/0.92  --inst_learning_start                   3000
% 2.67/0.92  --inst_learning_factor                  2
% 2.67/0.92  --inst_start_prop_sim_after_learn       3
% 2.67/0.92  --inst_sel_renew                        solver
% 2.67/0.92  --inst_lit_activity_flag                true
% 2.67/0.92  --inst_restr_to_given                   false
% 2.67/0.92  --inst_activity_threshold               500
% 2.67/0.92  --inst_out_proof                        true
% 2.67/0.92  
% 2.67/0.92  ------ Resolution Options
% 2.67/0.92  
% 2.67/0.92  --resolution_flag                       false
% 2.67/0.92  --res_lit_sel                           adaptive
% 2.67/0.92  --res_lit_sel_side                      none
% 2.67/0.92  --res_ordering                          kbo
% 2.67/0.92  --res_to_prop_solver                    active
% 2.67/0.92  --res_prop_simpl_new                    false
% 2.67/0.92  --res_prop_simpl_given                  true
% 2.67/0.92  --res_passive_queue_type                priority_queues
% 2.67/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.92  --res_passive_queues_freq               [15;5]
% 2.67/0.92  --res_forward_subs                      full
% 2.67/0.92  --res_backward_subs                     full
% 2.67/0.92  --res_forward_subs_resolution           true
% 2.67/0.92  --res_backward_subs_resolution          true
% 2.67/0.92  --res_orphan_elimination                true
% 2.67/0.92  --res_time_limit                        2.
% 2.67/0.92  --res_out_proof                         true
% 2.67/0.92  
% 2.67/0.92  ------ Superposition Options
% 2.67/0.92  
% 2.67/0.92  --superposition_flag                    true
% 2.67/0.92  --sup_passive_queue_type                priority_queues
% 2.67/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.92  --demod_completeness_check              fast
% 2.67/0.92  --demod_use_ground                      true
% 2.67/0.92  --sup_to_prop_solver                    passive
% 2.67/0.92  --sup_prop_simpl_new                    true
% 2.67/0.92  --sup_prop_simpl_given                  true
% 2.67/0.92  --sup_fun_splitting                     false
% 2.67/0.92  --sup_smt_interval                      50000
% 2.67/0.92  
% 2.67/0.92  ------ Superposition Simplification Setup
% 2.67/0.92  
% 2.67/0.92  --sup_indices_passive                   []
% 2.67/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.92  --sup_full_bw                           [BwDemod]
% 2.67/0.92  --sup_immed_triv                        [TrivRules]
% 2.67/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.92  --sup_immed_bw_main                     []
% 2.67/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.92  
% 2.67/0.92  ------ Combination Options
% 2.67/0.92  
% 2.67/0.92  --comb_res_mult                         3
% 2.67/0.92  --comb_sup_mult                         2
% 2.67/0.92  --comb_inst_mult                        10
% 2.67/0.92  
% 2.67/0.92  ------ Debug Options
% 2.67/0.92  
% 2.67/0.92  --dbg_backtrace                         false
% 2.67/0.92  --dbg_dump_prop_clauses                 false
% 2.67/0.92  --dbg_dump_prop_clauses_file            -
% 2.67/0.92  --dbg_out_stat                          false
% 2.67/0.92  
% 2.67/0.92  
% 2.67/0.92  
% 2.67/0.92  
% 2.67/0.92  ------ Proving...
% 2.67/0.92  
% 2.67/0.92  
% 2.67/0.92  % SZS status Theorem for theBenchmark.p
% 2.67/0.92  
% 2.67/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/0.92  
% 2.67/0.92  fof(f20,conjecture,(
% 2.67/0.92    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f21,negated_conjecture,(
% 2.67/0.92    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 2.67/0.92    inference(negated_conjecture,[],[f20])).
% 2.67/0.92  
% 2.67/0.92  fof(f25,plain,(
% 2.67/0.92    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 2.67/0.92    inference(ennf_transformation,[],[f21])).
% 2.67/0.92  
% 2.67/0.92  fof(f37,plain,(
% 2.67/0.92    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK3,sK4) = X0) )),
% 2.67/0.92    introduced(choice_axiom,[])).
% 2.67/0.92  
% 2.67/0.92  fof(f36,plain,(
% 2.67/0.92    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 2.67/0.92    introduced(choice_axiom,[])).
% 2.67/0.92  
% 2.67/0.92  fof(f38,plain,(
% 2.67/0.92    (k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & k4_tarski(sK3,sK4) = sK2),
% 2.67/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f37,f36])).
% 2.67/0.92  
% 2.67/0.92  fof(f78,plain,(
% 2.67/0.92    k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2),
% 2.67/0.92    inference(cnf_transformation,[],[f38])).
% 2.67/0.92  
% 2.67/0.92  fof(f77,plain,(
% 2.67/0.92    k4_tarski(sK3,sK4) = sK2),
% 2.67/0.92    inference(cnf_transformation,[],[f38])).
% 2.67/0.92  
% 2.67/0.92  fof(f19,axiom,(
% 2.67/0.92    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f75,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.67/0.92    inference(cnf_transformation,[],[f19])).
% 2.67/0.92  
% 2.67/0.92  fof(f76,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.67/0.92    inference(cnf_transformation,[],[f19])).
% 2.67/0.92  
% 2.67/0.92  fof(f16,axiom,(
% 2.67/0.92    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f57,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1))) )),
% 2.67/0.92    inference(cnf_transformation,[],[f16])).
% 2.67/0.92  
% 2.67/0.92  fof(f5,axiom,(
% 2.67/0.92    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f43,plain,(
% 2.67/0.92    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f5])).
% 2.67/0.92  
% 2.67/0.92  fof(f6,axiom,(
% 2.67/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f44,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f6])).
% 2.67/0.92  
% 2.67/0.92  fof(f7,axiom,(
% 2.67/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f45,plain,(
% 2.67/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f7])).
% 2.67/0.92  
% 2.67/0.92  fof(f8,axiom,(
% 2.67/0.92    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f46,plain,(
% 2.67/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f8])).
% 2.67/0.92  
% 2.67/0.92  fof(f9,axiom,(
% 2.67/0.92    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f47,plain,(
% 2.67/0.92    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f9])).
% 2.67/0.92  
% 2.67/0.92  fof(f10,axiom,(
% 2.67/0.92    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f48,plain,(
% 2.67/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f10])).
% 2.67/0.92  
% 2.67/0.92  fof(f11,axiom,(
% 2.67/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f49,plain,(
% 2.67/0.92    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f11])).
% 2.67/0.92  
% 2.67/0.92  fof(f79,plain,(
% 2.67/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.67/0.92    inference(definition_unfolding,[],[f48,f49])).
% 2.67/0.92  
% 2.67/0.92  fof(f80,plain,(
% 2.67/0.92    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.67/0.92    inference(definition_unfolding,[],[f47,f79])).
% 2.67/0.92  
% 2.67/0.92  fof(f81,plain,(
% 2.67/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.67/0.92    inference(definition_unfolding,[],[f46,f80])).
% 2.67/0.92  
% 2.67/0.92  fof(f82,plain,(
% 2.67/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.67/0.92    inference(definition_unfolding,[],[f45,f81])).
% 2.67/0.92  
% 2.67/0.92  fof(f83,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.67/0.92    inference(definition_unfolding,[],[f44,f82])).
% 2.67/0.92  
% 2.67/0.92  fof(f87,plain,(
% 2.67/0.92    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.67/0.92    inference(definition_unfolding,[],[f43,f83])).
% 2.67/0.92  
% 2.67/0.92  fof(f95,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.67/0.92    inference(definition_unfolding,[],[f57,f87,f87,f87])).
% 2.67/0.92  
% 2.67/0.92  fof(f14,axiom,(
% 2.67/0.92    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f23,plain,(
% 2.67/0.92    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 2.67/0.92    inference(ennf_transformation,[],[f14])).
% 2.67/0.92  
% 2.67/0.92  fof(f54,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 2.67/0.92    inference(cnf_transformation,[],[f23])).
% 2.67/0.92  
% 2.67/0.92  fof(f26,plain,(
% 2.67/0.92    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 2.67/0.92    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.67/0.92  
% 2.67/0.92  fof(f30,plain,(
% 2.67/0.92    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 2.67/0.92    inference(nnf_transformation,[],[f26])).
% 2.67/0.92  
% 2.67/0.92  fof(f31,plain,(
% 2.67/0.92    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 2.67/0.92    inference(flattening,[],[f30])).
% 2.67/0.92  
% 2.67/0.92  fof(f32,plain,(
% 2.67/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 2.67/0.92    inference(rectify,[],[f31])).
% 2.67/0.92  
% 2.67/0.92  fof(f33,plain,(
% 2.67/0.92    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 2.67/0.92    introduced(choice_axiom,[])).
% 2.67/0.92  
% 2.67/0.92  fof(f34,plain,(
% 2.67/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 2.67/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 2.67/0.92  
% 2.67/0.92  fof(f59,plain,(
% 2.67/0.92    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f34])).
% 2.67/0.92  
% 2.67/0.92  fof(f104,plain,(
% 2.67/0.92    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X0,X1,X2,X3,X4,X8,X6)) )),
% 2.67/0.92    inference(equality_resolution,[],[f59])).
% 2.67/0.92  
% 2.67/0.92  fof(f17,axiom,(
% 2.67/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f24,plain,(
% 2.67/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 2.67/0.92    inference(ennf_transformation,[],[f17])).
% 2.67/0.92  
% 2.67/0.92  fof(f27,plain,(
% 2.67/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 2.67/0.92    inference(definition_folding,[],[f24,f26])).
% 2.67/0.92  
% 2.67/0.92  fof(f35,plain,(
% 2.67/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 2.67/0.92    inference(nnf_transformation,[],[f27])).
% 2.67/0.92  
% 2.67/0.92  fof(f72,plain,(
% 2.67/0.92    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 2.67/0.92    inference(cnf_transformation,[],[f35])).
% 2.67/0.92  
% 2.67/0.92  fof(f97,plain,(
% 2.67/0.92    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 2.67/0.92    inference(definition_unfolding,[],[f72,f79])).
% 2.67/0.92  
% 2.67/0.92  fof(f105,plain,(
% 2.67/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 2.67/0.92    inference(equality_resolution,[],[f97])).
% 2.67/0.92  
% 2.67/0.92  fof(f15,axiom,(
% 2.67/0.92    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f29,plain,(
% 2.67/0.92    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 2.67/0.92    inference(nnf_transformation,[],[f15])).
% 2.67/0.92  
% 2.67/0.92  fof(f55,plain,(
% 2.67/0.92    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f29])).
% 2.67/0.92  
% 2.67/0.92  fof(f2,axiom,(
% 2.67/0.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f40,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.67/0.92    inference(cnf_transformation,[],[f2])).
% 2.67/0.92  
% 2.67/0.92  fof(f18,axiom,(
% 2.67/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f74,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.67/0.92    inference(cnf_transformation,[],[f18])).
% 2.67/0.92  
% 2.67/0.92  fof(f84,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.67/0.92    inference(definition_unfolding,[],[f74,f83])).
% 2.67/0.92  
% 2.67/0.92  fof(f85,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.67/0.92    inference(definition_unfolding,[],[f40,f84])).
% 2.67/0.92  
% 2.67/0.92  fof(f94,plain,(
% 2.67/0.92    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.67/0.92    inference(definition_unfolding,[],[f55,f85,f87,f87,f87])).
% 2.67/0.92  
% 2.67/0.92  fof(f98,plain,(
% 2.67/0.92    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 2.67/0.92    inference(equality_resolution,[],[f94])).
% 2.67/0.92  
% 2.67/0.92  fof(f1,axiom,(
% 2.67/0.92    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f22,plain,(
% 2.67/0.92    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.67/0.92    inference(rectify,[],[f1])).
% 2.67/0.92  
% 2.67/0.92  fof(f39,plain,(
% 2.67/0.92    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.67/0.92    inference(cnf_transformation,[],[f22])).
% 2.67/0.92  
% 2.67/0.92  fof(f88,plain,(
% 2.67/0.92    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.67/0.92    inference(definition_unfolding,[],[f39,f84])).
% 2.67/0.92  
% 2.67/0.92  fof(f4,axiom,(
% 2.67/0.92    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f42,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.67/0.92    inference(cnf_transformation,[],[f4])).
% 2.67/0.92  
% 2.67/0.92  fof(f13,axiom,(
% 2.67/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f52,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.67/0.92    inference(cnf_transformation,[],[f13])).
% 2.67/0.92  
% 2.67/0.92  fof(f86,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.67/0.92    inference(definition_unfolding,[],[f52,f83])).
% 2.67/0.92  
% 2.67/0.92  fof(f90,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0) )),
% 2.67/0.92    inference(definition_unfolding,[],[f42,f85,f86])).
% 2.67/0.92  
% 2.67/0.92  fof(f3,axiom,(
% 2.67/0.92    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f41,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.67/0.92    inference(cnf_transformation,[],[f3])).
% 2.67/0.92  
% 2.67/0.92  fof(f89,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0) )),
% 2.67/0.92    inference(definition_unfolding,[],[f41,f84,f86])).
% 2.67/0.92  
% 2.67/0.92  fof(f12,axiom,(
% 2.67/0.92    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/0.92  
% 2.67/0.92  fof(f28,plain,(
% 2.67/0.92    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.67/0.92    inference(nnf_transformation,[],[f12])).
% 2.67/0.92  
% 2.67/0.92  fof(f51,plain,(
% 2.67/0.92    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.67/0.92    inference(cnf_transformation,[],[f28])).
% 2.67/0.92  
% 2.67/0.92  fof(f91,plain,(
% 2.67/0.92    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.67/0.92    inference(definition_unfolding,[],[f51,f87])).
% 2.67/0.92  
% 2.67/0.92  fof(f53,plain,(
% 2.67/0.92    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 2.67/0.92    inference(cnf_transformation,[],[f23])).
% 2.67/0.92  
% 2.67/0.92  cnf(c_28,negated_conjecture,
% 2.67/0.92      ( k1_mcart_1(sK2) = sK2 | k2_mcart_1(sK2) = sK2 ),
% 2.67/0.92      inference(cnf_transformation,[],[f78]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_29,negated_conjecture,
% 2.67/0.92      ( k4_tarski(sK3,sK4) = sK2 ),
% 2.67/0.92      inference(cnf_transformation,[],[f77]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_27,plain,
% 2.67/0.92      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 2.67/0.92      inference(cnf_transformation,[],[f75]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3431,plain,
% 2.67/0.92      ( k1_mcart_1(sK2) = sK3 ),
% 2.67/0.92      inference(superposition,[status(thm)],[c_29,c_27]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3442,plain,
% 2.67/0.92      ( k2_mcart_1(sK2) = sK2 | sK3 = sK2 ),
% 2.67/0.92      inference(superposition,[status(thm)],[c_28,c_3431]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_26,plain,
% 2.67/0.92      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 2.67/0.92      inference(cnf_transformation,[],[f76]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3428,plain,
% 2.67/0.92      ( k2_mcart_1(sK2) = sK4 ),
% 2.67/0.92      inference(superposition,[status(thm)],[c_29,c_26]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3444,plain,
% 2.67/0.92      ( sK4 = sK2 | sK3 = sK2 ),
% 2.67/0.92      inference(demodulation,[status(thm)],[c_3442,c_3428]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3447,plain,
% 2.67/0.92      ( k4_tarski(sK3,sK2) = sK2 | sK3 = sK2 ),
% 2.67/0.92      inference(superposition,[status(thm)],[c_3444,c_29]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_9,plain,
% 2.67/0.92      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 2.67/0.92      inference(cnf_transformation,[],[f95]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3660,plain,
% 2.67/0.92      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 2.67/0.92      | sK3 = sK2 ),
% 2.67/0.92      inference(superposition,[status(thm)],[c_3447,c_9]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_5,plain,
% 2.67/0.92      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 2.67/0.92      inference(cnf_transformation,[],[f54]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3235,plain,
% 2.67/0.92      ( k1_xboole_0 = X0
% 2.67/0.92      | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 2.67/0.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3966,plain,
% 2.67/0.92      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 2.67/0.92      | sK3 = sK2
% 2.67/0.92      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 2.67/0.92      inference(superposition,[status(thm)],[c_3660,c_3235]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_22,plain,
% 2.67/0.92      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X5,X6) ),
% 2.67/0.92      inference(cnf_transformation,[],[f104]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_25,plain,
% 2.67/0.92      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
% 2.67/0.92      inference(cnf_transformation,[],[f105]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_1285,plain,
% 2.67/0.92      ( r2_hidden(X0,X1)
% 2.67/0.92      | X2 != X3
% 2.67/0.92      | X4 != X0
% 2.67/0.92      | X5 != X6
% 2.67/0.92      | X7 != X8
% 2.67/0.92      | X9 != X10
% 2.67/0.92      | X11 != X12
% 2.67/0.92      | k6_enumset1(X4,X4,X4,X5,X7,X9,X11,X2) != X1 ),
% 2.67/0.92      inference(resolution_lifted,[status(thm)],[c_22,c_25]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_1286,plain,
% 2.67/0.92      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
% 2.67/0.92      inference(unflattening,[status(thm)],[c_1285]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_1287,plain,
% 2.67/0.92      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 2.67/0.92      inference(predicate_to_equality,[status(thm)],[c_1286]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_1289,plain,
% 2.67/0.92      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.67/0.92      inference(instantiation,[status(thm)],[c_1287]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_8,plain,
% 2.67/0.92      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.67/0.92      inference(cnf_transformation,[],[f98]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_0,plain,
% 2.67/0.92      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 2.67/0.92      inference(cnf_transformation,[],[f88]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_2,plain,
% 2.67/0.92      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
% 2.67/0.92      inference(cnf_transformation,[],[f90]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_1,plain,
% 2.67/0.92      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
% 2.67/0.92      inference(cnf_transformation,[],[f89]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3298,plain,
% 2.67/0.92      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.67/0.92      inference(light_normalisation,[status(thm)],[c_2,c_1]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3371,plain,
% 2.67/0.92      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 2.67/0.92      inference(demodulation,[status(thm)],[c_8,c_0,c_3298]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3391,plain,
% 2.67/0.92      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
% 2.67/0.92      inference(instantiation,[status(thm)],[c_3371]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3,plain,
% 2.67/0.92      ( ~ r2_hidden(X0,X1)
% 2.67/0.92      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 2.67/0.92      inference(cnf_transformation,[],[f91]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3552,plain,
% 2.67/0.92      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))
% 2.67/0.92      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
% 2.67/0.92      inference(instantiation,[status(thm)],[c_3]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3556,plain,
% 2.67/0.92      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) != iProver_top
% 2.67/0.92      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 2.67/0.92      inference(predicate_to_equality,[status(thm)],[c_3552]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3558,plain,
% 2.67/0.92      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 2.67/0.92      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.67/0.92      inference(instantiation,[status(thm)],[c_3556]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_4062,plain,
% 2.67/0.92      ( sK3 = sK2 ),
% 2.67/0.92      inference(global_propositional_subsumption,
% 2.67/0.92                [status(thm)],
% 2.67/0.92                [c_3966,c_1289,c_3391,c_3558]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3659,plain,
% 2.67/0.92      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 2.67/0.92      inference(superposition,[status(thm)],[c_29,c_9]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_6,plain,
% 2.67/0.92      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 2.67/0.92      inference(cnf_transformation,[],[f53]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3234,plain,
% 2.67/0.92      ( k1_xboole_0 = X0
% 2.67/0.92      | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.67/0.92      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_3815,plain,
% 2.67/0.92      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 2.67/0.92      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 2.67/0.92      inference(superposition,[status(thm)],[c_3659,c_3234]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(c_4065,plain,
% 2.67/0.92      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 2.67/0.92      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 2.67/0.92      inference(demodulation,[status(thm)],[c_4062,c_3815]) ).
% 2.67/0.92  
% 2.67/0.92  cnf(contradiction,plain,
% 2.67/0.92      ( $false ),
% 2.67/0.92      inference(minisat,[status(thm)],[c_4065,c_3558,c_3391,c_1289]) ).
% 2.67/0.92  
% 2.67/0.92  
% 2.67/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/0.92  
% 2.67/0.92  ------                               Statistics
% 2.67/0.92  
% 2.67/0.92  ------ General
% 2.67/0.92  
% 2.67/0.92  abstr_ref_over_cycles:                  0
% 2.67/0.92  abstr_ref_under_cycles:                 0
% 2.67/0.92  gc_basic_clause_elim:                   0
% 2.67/0.92  forced_gc_time:                         0
% 2.67/0.92  parsing_time:                           0.009
% 2.67/0.92  unif_index_cands_time:                  0.
% 2.67/0.92  unif_index_add_time:                    0.
% 2.67/0.92  orderings_time:                         0.
% 2.67/0.92  out_proof_time:                         0.008
% 2.67/0.92  total_time:                             0.145
% 2.67/0.92  num_of_symbols:                         47
% 2.67/0.92  num_of_terms:                           2946
% 2.67/0.92  
% 2.67/0.92  ------ Preprocessing
% 2.67/0.92  
% 2.67/0.92  num_of_splits:                          0
% 2.67/0.92  num_of_split_atoms:                     0
% 2.67/0.92  num_of_reused_defs:                     0
% 2.67/0.92  num_eq_ax_congr_red:                    28
% 2.67/0.92  num_of_sem_filtered_clauses:            1
% 2.67/0.92  num_of_subtypes:                        0
% 2.67/0.92  monotx_restored_types:                  0
% 2.67/0.92  sat_num_of_epr_types:                   0
% 2.67/0.92  sat_num_of_non_cyclic_types:            0
% 2.67/0.92  sat_guarded_non_collapsed_types:        0
% 2.67/0.92  num_pure_diseq_elim:                    0
% 2.67/0.92  simp_replaced_by:                       0
% 2.67/0.92  res_preprocessed:                       117
% 2.67/0.92  prep_upred:                             0
% 2.67/0.92  prep_unflattend:                        174
% 2.67/0.92  smt_new_axioms:                         0
% 2.67/0.92  pred_elim_cands:                        3
% 2.67/0.92  pred_elim:                              0
% 2.67/0.92  pred_elim_cl:                           0
% 2.67/0.92  pred_elim_cycles:                       3
% 2.67/0.92  merged_defs:                            6
% 2.67/0.92  merged_defs_ncl:                        0
% 2.67/0.92  bin_hyper_res:                          6
% 2.67/0.92  prep_cycles:                            3
% 2.67/0.92  pred_elim_time:                         0.035
% 2.67/0.92  splitting_time:                         0.
% 2.67/0.92  sem_filter_time:                        0.
% 2.67/0.92  monotx_time:                            0.
% 2.67/0.92  subtype_inf_time:                       0.
% 2.67/0.92  
% 2.67/0.92  ------ Problem properties
% 2.67/0.92  
% 2.67/0.92  clauses:                                30
% 2.67/0.92  conjectures:                            2
% 2.67/0.92  epr:                                    7
% 2.67/0.92  horn:                                   26
% 2.67/0.92  ground:                                 2
% 2.67/0.92  unary:                                  9
% 2.67/0.92  binary:                                 13
% 2.67/0.92  lits:                                   69
% 2.67/0.92  lits_eq:                                33
% 2.67/0.92  fd_pure:                                0
% 2.67/0.92  fd_pseudo:                              0
% 2.67/0.92  fd_cond:                                2
% 2.67/0.92  fd_pseudo_cond:                         3
% 2.67/0.92  ac_symbols:                             0
% 2.67/0.92  
% 2.67/0.92  ------ Propositional Solver
% 2.67/0.92  
% 2.67/0.92  prop_solver_calls:                      20
% 2.67/0.92  prop_fast_solver_calls:                 1091
% 2.67/0.92  smt_solver_calls:                       0
% 2.67/0.92  smt_fast_solver_calls:                  0
% 2.67/0.92  prop_num_of_clauses:                    737
% 2.67/0.92  prop_preprocess_simplified:             4224
% 2.67/0.92  prop_fo_subsumed:                       2
% 2.67/0.92  prop_solver_time:                       0.
% 2.67/0.92  smt_solver_time:                        0.
% 2.67/0.92  smt_fast_solver_time:                   0.
% 2.67/0.92  prop_fast_solver_time:                  0.
% 2.67/0.92  prop_unsat_core_time:                   0.
% 2.67/0.92  
% 2.67/0.92  ------ QBF
% 2.67/0.92  
% 2.67/0.92  qbf_q_res:                              0
% 2.67/0.92  qbf_num_tautologies:                    0
% 2.67/0.92  qbf_prep_cycles:                        0
% 2.67/0.92  
% 2.67/0.92  ------ BMC1
% 2.67/0.92  
% 2.67/0.92  bmc1_current_bound:                     -1
% 2.67/0.92  bmc1_last_solved_bound:                 -1
% 2.67/0.92  bmc1_unsat_core_size:                   -1
% 2.67/0.92  bmc1_unsat_core_parents_size:           -1
% 2.67/0.92  bmc1_merge_next_fun:                    0
% 2.67/0.92  bmc1_unsat_core_clauses_time:           0.
% 2.67/0.92  
% 2.67/0.92  ------ Instantiation
% 2.67/0.92  
% 2.67/0.92  inst_num_of_clauses:                    154
% 2.67/0.92  inst_num_in_passive:                    2
% 2.67/0.92  inst_num_in_active:                     86
% 2.67/0.92  inst_num_in_unprocessed:                66
% 2.67/0.92  inst_num_of_loops:                      100
% 2.67/0.92  inst_num_of_learning_restarts:          0
% 2.67/0.92  inst_num_moves_active_passive:          13
% 2.67/0.92  inst_lit_activity:                      0
% 2.67/0.92  inst_lit_activity_moves:                0
% 2.67/0.92  inst_num_tautologies:                   0
% 2.67/0.92  inst_num_prop_implied:                  0
% 2.67/0.92  inst_num_existing_simplified:           0
% 2.67/0.92  inst_num_eq_res_simplified:             0
% 2.67/0.92  inst_num_child_elim:                    0
% 2.67/0.92  inst_num_of_dismatching_blockings:      17
% 2.67/0.92  inst_num_of_non_proper_insts:           70
% 2.67/0.92  inst_num_of_duplicates:                 0
% 2.67/0.92  inst_inst_num_from_inst_to_res:         0
% 2.67/0.92  inst_dismatching_checking_time:         0.
% 2.67/0.92  
% 2.67/0.92  ------ Resolution
% 2.67/0.92  
% 2.67/0.92  res_num_of_clauses:                     0
% 2.67/0.92  res_num_in_passive:                     0
% 2.67/0.92  res_num_in_active:                      0
% 2.67/0.92  res_num_of_loops:                       120
% 2.67/0.92  res_forward_subset_subsumed:            6
% 2.67/0.92  res_backward_subset_subsumed:           0
% 2.67/0.92  res_forward_subsumed:                   0
% 2.67/0.92  res_backward_subsumed:                  0
% 2.67/0.92  res_forward_subsumption_resolution:     0
% 2.67/0.92  res_backward_subsumption_resolution:    0
% 2.67/0.92  res_clause_to_clause_subsumption:       1556
% 2.67/0.92  res_orphan_elimination:                 0
% 2.67/0.92  res_tautology_del:                      23
% 2.67/0.92  res_num_eq_res_simplified:              0
% 2.67/0.92  res_num_sel_changes:                    0
% 2.67/0.92  res_moves_from_active_to_pass:          0
% 2.67/0.92  
% 2.67/0.92  ------ Superposition
% 2.67/0.92  
% 2.67/0.92  sup_time_total:                         0.
% 2.67/0.92  sup_time_generating:                    0.
% 2.67/0.92  sup_time_sim_full:                      0.
% 2.67/0.92  sup_time_sim_immed:                     0.
% 2.67/0.92  
% 2.67/0.92  sup_num_of_clauses:                     39
% 2.67/0.92  sup_num_in_active:                      13
% 2.67/0.92  sup_num_in_passive:                     26
% 2.67/0.92  sup_num_of_loops:                       19
% 2.67/0.92  sup_fw_superposition:                   49
% 2.67/0.92  sup_bw_superposition:                   6
% 2.67/0.92  sup_immediate_simplified:               4
% 2.67/0.92  sup_given_eliminated:                   0
% 2.67/0.92  comparisons_done:                       0
% 2.67/0.92  comparisons_avoided:                    5
% 2.67/0.92  
% 2.67/0.92  ------ Simplifications
% 2.67/0.92  
% 2.67/0.92  
% 2.67/0.92  sim_fw_subset_subsumed:                 1
% 2.67/0.92  sim_bw_subset_subsumed:                 0
% 2.67/0.92  sim_fw_subsumed:                        0
% 2.67/0.92  sim_bw_subsumed:                        1
% 2.67/0.92  sim_fw_subsumption_res:                 0
% 2.67/0.92  sim_bw_subsumption_res:                 0
% 2.67/0.92  sim_tautology_del:                      0
% 2.67/0.92  sim_eq_tautology_del:                   3
% 2.67/0.92  sim_eq_res_simp:                        0
% 2.67/0.92  sim_fw_demodulated:                     2
% 2.67/0.92  sim_bw_demodulated:                     6
% 2.67/0.92  sim_light_normalised:                   2
% 2.67/0.92  sim_joinable_taut:                      0
% 2.67/0.92  sim_joinable_simp:                      0
% 2.67/0.92  sim_ac_normalised:                      0
% 2.67/0.92  sim_smt_subsumption:                    0
% 2.67/0.92  
%------------------------------------------------------------------------------
