%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:57 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 839 expanded)
%              Number of clauses        :   43 (  78 expanded)
%              Number of leaves         :   24 ( 268 expanded)
%              Depth                    :   16
%              Number of atoms          :  359 (1450 expanded)
%              Number of equality atoms :  289 (1311 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f79,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f19])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f84])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f83])).

fof(f97,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f57,f84,f88,f84])).

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

fof(f60,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X0,X1,X2,X3,X4,X8,X6) ) ),
    inference(equality_resolution,[],[f60])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f73,f80])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f99])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f85])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f55,f86,f88,f88,f88])).

fof(f100,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f95])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f85])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f84])).

fof(f91,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f42,f86,f87])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f90,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f41,f85,f87])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f88])).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f96,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f58,f84,f84,f88])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_29,negated_conjecture,
    ( k1_mcart_1(sK2) = sK2
    | k2_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3437,plain,
    ( k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_30,c_28])).

cnf(c_3448,plain,
    ( k2_mcart_1(sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_29,c_3437])).

cnf(c_27,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3434,plain,
    ( k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_30,c_27])).

cnf(c_3450,plain,
    ( sK4 = sK2
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_3448,c_3434])).

cnf(c_3453,plain,
    ( k4_tarski(sK3,sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_3450,c_30])).

cnf(c_10,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3737,plain,
    ( k6_enumset1(k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),sK2) = k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) ),
    inference(superposition,[status(thm)],[c_30,c_10])).

cnf(c_4001,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_3453,c_3737])).

cnf(c_23,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X5,X6) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_26,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1287,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | X11 != X12
    | k6_enumset1(X4,X4,X4,X5,X7,X9,X11,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_1288,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(unflattening,[status(thm)],[c_1287])).

cnf(c_1289,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_1291,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1289])).

cnf(c_8,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3302,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_1])).

cnf(c_3377,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8,c_0,c_3302])).

cnf(c_3385,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3377])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3564,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3568,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3564])).

cnf(c_3570,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3568])).

cnf(c_9,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3631,plain,
    ( k6_enumset1(k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),sK2) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_30,c_9])).

cnf(c_3897,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_30,c_3631])).

cnf(c_3971,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_3450,c_3897])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3239,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4791,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK3 = sK2
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3971,c_3239])).

cnf(c_5826,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4001,c_1291,c_3385,c_3570,c_4791])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3238,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4550,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3897,c_3238])).

cnf(c_4993,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4550,c_3377])).

cnf(c_5832,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5826,c_4993])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5832,c_3570,c_1291])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:35:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.14/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.00  
% 3.14/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/1.00  
% 3.14/1.00  ------  iProver source info
% 3.14/1.00  
% 3.14/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.14/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/1.00  git: non_committed_changes: false
% 3.14/1.00  git: last_make_outside_of_git: false
% 3.14/1.00  
% 3.14/1.00  ------ 
% 3.14/1.00  
% 3.14/1.00  ------ Input Options
% 3.14/1.00  
% 3.14/1.00  --out_options                           all
% 3.14/1.00  --tptp_safe_out                         true
% 3.14/1.00  --problem_path                          ""
% 3.14/1.00  --include_path                          ""
% 3.14/1.00  --clausifier                            res/vclausify_rel
% 3.14/1.00  --clausifier_options                    --mode clausify
% 3.14/1.00  --stdin                                 false
% 3.14/1.00  --stats_out                             all
% 3.14/1.00  
% 3.14/1.00  ------ General Options
% 3.14/1.00  
% 3.14/1.00  --fof                                   false
% 3.14/1.00  --time_out_real                         305.
% 3.14/1.00  --time_out_virtual                      -1.
% 3.14/1.00  --symbol_type_check                     false
% 3.14/1.00  --clausify_out                          false
% 3.14/1.00  --sig_cnt_out                           false
% 3.14/1.00  --trig_cnt_out                          false
% 3.14/1.00  --trig_cnt_out_tolerance                1.
% 3.14/1.00  --trig_cnt_out_sk_spl                   false
% 3.14/1.00  --abstr_cl_out                          false
% 3.14/1.00  
% 3.14/1.00  ------ Global Options
% 3.14/1.00  
% 3.14/1.00  --schedule                              default
% 3.14/1.00  --add_important_lit                     false
% 3.14/1.00  --prop_solver_per_cl                    1000
% 3.14/1.00  --min_unsat_core                        false
% 3.14/1.00  --soft_assumptions                      false
% 3.14/1.00  --soft_lemma_size                       3
% 3.14/1.00  --prop_impl_unit_size                   0
% 3.14/1.00  --prop_impl_unit                        []
% 3.14/1.00  --share_sel_clauses                     true
% 3.14/1.00  --reset_solvers                         false
% 3.14/1.00  --bc_imp_inh                            [conj_cone]
% 3.14/1.00  --conj_cone_tolerance                   3.
% 3.14/1.00  --extra_neg_conj                        none
% 3.14/1.00  --large_theory_mode                     true
% 3.14/1.00  --prolific_symb_bound                   200
% 3.14/1.00  --lt_threshold                          2000
% 3.14/1.00  --clause_weak_htbl                      true
% 3.14/1.00  --gc_record_bc_elim                     false
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing Options
% 3.14/1.00  
% 3.14/1.00  --preprocessing_flag                    true
% 3.14/1.00  --time_out_prep_mult                    0.1
% 3.14/1.00  --splitting_mode                        input
% 3.14/1.00  --splitting_grd                         true
% 3.14/1.00  --splitting_cvd                         false
% 3.14/1.00  --splitting_cvd_svl                     false
% 3.14/1.00  --splitting_nvd                         32
% 3.14/1.00  --sub_typing                            true
% 3.14/1.00  --prep_gs_sim                           true
% 3.14/1.00  --prep_unflatten                        true
% 3.14/1.00  --prep_res_sim                          true
% 3.14/1.00  --prep_upred                            true
% 3.14/1.00  --prep_sem_filter                       exhaustive
% 3.14/1.00  --prep_sem_filter_out                   false
% 3.14/1.00  --pred_elim                             true
% 3.14/1.00  --res_sim_input                         true
% 3.14/1.00  --eq_ax_congr_red                       true
% 3.14/1.00  --pure_diseq_elim                       true
% 3.14/1.00  --brand_transform                       false
% 3.14/1.00  --non_eq_to_eq                          false
% 3.14/1.00  --prep_def_merge                        true
% 3.14/1.00  --prep_def_merge_prop_impl              false
% 3.14/1.00  --prep_def_merge_mbd                    true
% 3.14/1.00  --prep_def_merge_tr_red                 false
% 3.14/1.00  --prep_def_merge_tr_cl                  false
% 3.14/1.00  --smt_preprocessing                     true
% 3.14/1.00  --smt_ac_axioms                         fast
% 3.14/1.00  --preprocessed_out                      false
% 3.14/1.00  --preprocessed_stats                    false
% 3.14/1.00  
% 3.14/1.00  ------ Abstraction refinement Options
% 3.14/1.00  
% 3.14/1.00  --abstr_ref                             []
% 3.14/1.00  --abstr_ref_prep                        false
% 3.14/1.00  --abstr_ref_until_sat                   false
% 3.14/1.00  --abstr_ref_sig_restrict                funpre
% 3.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/1.00  --abstr_ref_under                       []
% 3.14/1.00  
% 3.14/1.00  ------ SAT Options
% 3.14/1.00  
% 3.14/1.00  --sat_mode                              false
% 3.14/1.00  --sat_fm_restart_options                ""
% 3.14/1.00  --sat_gr_def                            false
% 3.14/1.00  --sat_epr_types                         true
% 3.14/1.00  --sat_non_cyclic_types                  false
% 3.14/1.00  --sat_finite_models                     false
% 3.14/1.00  --sat_fm_lemmas                         false
% 3.14/1.00  --sat_fm_prep                           false
% 3.14/1.00  --sat_fm_uc_incr                        true
% 3.14/1.00  --sat_out_model                         small
% 3.14/1.00  --sat_out_clauses                       false
% 3.14/1.00  
% 3.14/1.00  ------ QBF Options
% 3.14/1.00  
% 3.14/1.00  --qbf_mode                              false
% 3.14/1.00  --qbf_elim_univ                         false
% 3.14/1.00  --qbf_dom_inst                          none
% 3.14/1.00  --qbf_dom_pre_inst                      false
% 3.14/1.00  --qbf_sk_in                             false
% 3.14/1.00  --qbf_pred_elim                         true
% 3.14/1.00  --qbf_split                             512
% 3.14/1.00  
% 3.14/1.00  ------ BMC1 Options
% 3.14/1.00  
% 3.14/1.00  --bmc1_incremental                      false
% 3.14/1.00  --bmc1_axioms                           reachable_all
% 3.14/1.00  --bmc1_min_bound                        0
% 3.14/1.00  --bmc1_max_bound                        -1
% 3.14/1.00  --bmc1_max_bound_default                -1
% 3.14/1.00  --bmc1_symbol_reachability              true
% 3.14/1.00  --bmc1_property_lemmas                  false
% 3.14/1.00  --bmc1_k_induction                      false
% 3.14/1.00  --bmc1_non_equiv_states                 false
% 3.14/1.00  --bmc1_deadlock                         false
% 3.14/1.00  --bmc1_ucm                              false
% 3.14/1.00  --bmc1_add_unsat_core                   none
% 3.14/1.00  --bmc1_unsat_core_children              false
% 3.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/1.00  --bmc1_out_stat                         full
% 3.14/1.00  --bmc1_ground_init                      false
% 3.14/1.00  --bmc1_pre_inst_next_state              false
% 3.14/1.00  --bmc1_pre_inst_state                   false
% 3.14/1.00  --bmc1_pre_inst_reach_state             false
% 3.14/1.00  --bmc1_out_unsat_core                   false
% 3.14/1.00  --bmc1_aig_witness_out                  false
% 3.14/1.00  --bmc1_verbose                          false
% 3.14/1.00  --bmc1_dump_clauses_tptp                false
% 3.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.14/1.00  --bmc1_dump_file                        -
% 3.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.14/1.00  --bmc1_ucm_extend_mode                  1
% 3.14/1.00  --bmc1_ucm_init_mode                    2
% 3.14/1.00  --bmc1_ucm_cone_mode                    none
% 3.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.14/1.00  --bmc1_ucm_relax_model                  4
% 3.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/1.00  --bmc1_ucm_layered_model                none
% 3.14/1.00  --bmc1_ucm_max_lemma_size               10
% 3.14/1.00  
% 3.14/1.00  ------ AIG Options
% 3.14/1.00  
% 3.14/1.00  --aig_mode                              false
% 3.14/1.00  
% 3.14/1.00  ------ Instantiation Options
% 3.14/1.00  
% 3.14/1.00  --instantiation_flag                    true
% 3.14/1.00  --inst_sos_flag                         false
% 3.14/1.00  --inst_sos_phase                        true
% 3.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/1.00  --inst_lit_sel_side                     num_symb
% 3.14/1.00  --inst_solver_per_active                1400
% 3.14/1.00  --inst_solver_calls_frac                1.
% 3.14/1.00  --inst_passive_queue_type               priority_queues
% 3.14/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/1.00  --inst_passive_queues_freq              [25;2]
% 3.14/1.00  --inst_dismatching                      true
% 3.14/1.00  --inst_eager_unprocessed_to_passive     true
% 3.14/1.00  --inst_prop_sim_given                   true
% 3.14/1.00  --inst_prop_sim_new                     false
% 3.14/1.00  --inst_subs_new                         false
% 3.14/1.00  --inst_eq_res_simp                      false
% 3.14/1.00  --inst_subs_given                       false
% 3.14/1.00  --inst_orphan_elimination               true
% 3.14/1.00  --inst_learning_loop_flag               true
% 3.14/1.00  --inst_learning_start                   3000
% 3.14/1.00  --inst_learning_factor                  2
% 3.14/1.00  --inst_start_prop_sim_after_learn       3
% 3.14/1.00  --inst_sel_renew                        solver
% 3.14/1.00  --inst_lit_activity_flag                true
% 3.14/1.00  --inst_restr_to_given                   false
% 3.14/1.00  --inst_activity_threshold               500
% 3.14/1.00  --inst_out_proof                        true
% 3.14/1.00  
% 3.14/1.00  ------ Resolution Options
% 3.14/1.00  
% 3.14/1.00  --resolution_flag                       true
% 3.14/1.00  --res_lit_sel                           adaptive
% 3.14/1.00  --res_lit_sel_side                      none
% 3.14/1.00  --res_ordering                          kbo
% 3.14/1.00  --res_to_prop_solver                    active
% 3.14/1.00  --res_prop_simpl_new                    false
% 3.14/1.00  --res_prop_simpl_given                  true
% 3.14/1.00  --res_passive_queue_type                priority_queues
% 3.14/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/1.00  --res_passive_queues_freq               [15;5]
% 3.14/1.00  --res_forward_subs                      full
% 3.14/1.00  --res_backward_subs                     full
% 3.14/1.00  --res_forward_subs_resolution           true
% 3.14/1.00  --res_backward_subs_resolution          true
% 3.14/1.00  --res_orphan_elimination                true
% 3.14/1.00  --res_time_limit                        2.
% 3.14/1.00  --res_out_proof                         true
% 3.14/1.00  
% 3.14/1.00  ------ Superposition Options
% 3.14/1.00  
% 3.14/1.00  --superposition_flag                    true
% 3.14/1.00  --sup_passive_queue_type                priority_queues
% 3.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.14/1.00  --demod_completeness_check              fast
% 3.14/1.00  --demod_use_ground                      true
% 3.14/1.00  --sup_to_prop_solver                    passive
% 3.14/1.00  --sup_prop_simpl_new                    true
% 3.14/1.00  --sup_prop_simpl_given                  true
% 3.14/1.00  --sup_fun_splitting                     false
% 3.14/1.00  --sup_smt_interval                      50000
% 3.14/1.00  
% 3.14/1.00  ------ Superposition Simplification Setup
% 3.14/1.00  
% 3.14/1.00  --sup_indices_passive                   []
% 3.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_full_bw                           [BwDemod]
% 3.14/1.00  --sup_immed_triv                        [TrivRules]
% 3.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_immed_bw_main                     []
% 3.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.00  
% 3.14/1.00  ------ Combination Options
% 3.14/1.00  
% 3.14/1.00  --comb_res_mult                         3
% 3.14/1.00  --comb_sup_mult                         2
% 3.14/1.00  --comb_inst_mult                        10
% 3.14/1.00  
% 3.14/1.00  ------ Debug Options
% 3.14/1.00  
% 3.14/1.00  --dbg_backtrace                         false
% 3.14/1.00  --dbg_dump_prop_clauses                 false
% 3.14/1.00  --dbg_dump_prop_clauses_file            -
% 3.14/1.00  --dbg_out_stat                          false
% 3.14/1.00  ------ Parsing...
% 3.14/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/1.00  ------ Proving...
% 3.14/1.00  ------ Problem Properties 
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  clauses                                 31
% 3.14/1.00  conjectures                             2
% 3.14/1.00  EPR                                     7
% 3.14/1.00  Horn                                    27
% 3.14/1.00  unary                                   10
% 3.14/1.00  binary                                  13
% 3.14/1.00  lits                                    70
% 3.14/1.00  lits eq                                 34
% 3.14/1.00  fd_pure                                 0
% 3.14/1.00  fd_pseudo                               0
% 3.14/1.00  fd_cond                                 2
% 3.14/1.00  fd_pseudo_cond                          3
% 3.14/1.00  AC symbols                              0
% 3.14/1.00  
% 3.14/1.00  ------ Schedule dynamic 5 is on 
% 3.14/1.00  
% 3.14/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  ------ 
% 3.14/1.00  Current options:
% 3.14/1.00  ------ 
% 3.14/1.00  
% 3.14/1.00  ------ Input Options
% 3.14/1.00  
% 3.14/1.00  --out_options                           all
% 3.14/1.00  --tptp_safe_out                         true
% 3.14/1.00  --problem_path                          ""
% 3.14/1.00  --include_path                          ""
% 3.14/1.00  --clausifier                            res/vclausify_rel
% 3.14/1.00  --clausifier_options                    --mode clausify
% 3.14/1.00  --stdin                                 false
% 3.14/1.00  --stats_out                             all
% 3.14/1.00  
% 3.14/1.00  ------ General Options
% 3.14/1.00  
% 3.14/1.00  --fof                                   false
% 3.14/1.00  --time_out_real                         305.
% 3.14/1.00  --time_out_virtual                      -1.
% 3.14/1.00  --symbol_type_check                     false
% 3.14/1.00  --clausify_out                          false
% 3.14/1.00  --sig_cnt_out                           false
% 3.14/1.00  --trig_cnt_out                          false
% 3.14/1.00  --trig_cnt_out_tolerance                1.
% 3.14/1.00  --trig_cnt_out_sk_spl                   false
% 3.14/1.00  --abstr_cl_out                          false
% 3.14/1.00  
% 3.14/1.00  ------ Global Options
% 3.14/1.00  
% 3.14/1.00  --schedule                              default
% 3.14/1.00  --add_important_lit                     false
% 3.14/1.00  --prop_solver_per_cl                    1000
% 3.14/1.00  --min_unsat_core                        false
% 3.14/1.00  --soft_assumptions                      false
% 3.14/1.00  --soft_lemma_size                       3
% 3.14/1.00  --prop_impl_unit_size                   0
% 3.14/1.00  --prop_impl_unit                        []
% 3.14/1.00  --share_sel_clauses                     true
% 3.14/1.00  --reset_solvers                         false
% 3.14/1.00  --bc_imp_inh                            [conj_cone]
% 3.14/1.00  --conj_cone_tolerance                   3.
% 3.14/1.00  --extra_neg_conj                        none
% 3.14/1.00  --large_theory_mode                     true
% 3.14/1.00  --prolific_symb_bound                   200
% 3.14/1.00  --lt_threshold                          2000
% 3.14/1.00  --clause_weak_htbl                      true
% 3.14/1.00  --gc_record_bc_elim                     false
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing Options
% 3.14/1.00  
% 3.14/1.00  --preprocessing_flag                    true
% 3.14/1.00  --time_out_prep_mult                    0.1
% 3.14/1.00  --splitting_mode                        input
% 3.14/1.00  --splitting_grd                         true
% 3.14/1.00  --splitting_cvd                         false
% 3.14/1.00  --splitting_cvd_svl                     false
% 3.14/1.00  --splitting_nvd                         32
% 3.14/1.00  --sub_typing                            true
% 3.14/1.00  --prep_gs_sim                           true
% 3.14/1.00  --prep_unflatten                        true
% 3.14/1.00  --prep_res_sim                          true
% 3.14/1.00  --prep_upred                            true
% 3.14/1.00  --prep_sem_filter                       exhaustive
% 3.14/1.00  --prep_sem_filter_out                   false
% 3.14/1.00  --pred_elim                             true
% 3.14/1.00  --res_sim_input                         true
% 3.14/1.00  --eq_ax_congr_red                       true
% 3.14/1.00  --pure_diseq_elim                       true
% 3.14/1.00  --brand_transform                       false
% 3.14/1.00  --non_eq_to_eq                          false
% 3.14/1.00  --prep_def_merge                        true
% 3.14/1.00  --prep_def_merge_prop_impl              false
% 3.14/1.00  --prep_def_merge_mbd                    true
% 3.14/1.00  --prep_def_merge_tr_red                 false
% 3.14/1.00  --prep_def_merge_tr_cl                  false
% 3.14/1.00  --smt_preprocessing                     true
% 3.14/1.00  --smt_ac_axioms                         fast
% 3.14/1.00  --preprocessed_out                      false
% 3.14/1.00  --preprocessed_stats                    false
% 3.14/1.00  
% 3.14/1.00  ------ Abstraction refinement Options
% 3.14/1.00  
% 3.14/1.00  --abstr_ref                             []
% 3.14/1.00  --abstr_ref_prep                        false
% 3.14/1.00  --abstr_ref_until_sat                   false
% 3.14/1.00  --abstr_ref_sig_restrict                funpre
% 3.14/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/1.00  --abstr_ref_under                       []
% 3.14/1.00  
% 3.14/1.00  ------ SAT Options
% 3.14/1.00  
% 3.14/1.00  --sat_mode                              false
% 3.14/1.00  --sat_fm_restart_options                ""
% 3.14/1.00  --sat_gr_def                            false
% 3.14/1.00  --sat_epr_types                         true
% 3.14/1.00  --sat_non_cyclic_types                  false
% 3.14/1.00  --sat_finite_models                     false
% 3.14/1.00  --sat_fm_lemmas                         false
% 3.14/1.00  --sat_fm_prep                           false
% 3.14/1.00  --sat_fm_uc_incr                        true
% 3.14/1.00  --sat_out_model                         small
% 3.14/1.00  --sat_out_clauses                       false
% 3.14/1.00  
% 3.14/1.00  ------ QBF Options
% 3.14/1.00  
% 3.14/1.00  --qbf_mode                              false
% 3.14/1.00  --qbf_elim_univ                         false
% 3.14/1.00  --qbf_dom_inst                          none
% 3.14/1.00  --qbf_dom_pre_inst                      false
% 3.14/1.00  --qbf_sk_in                             false
% 3.14/1.00  --qbf_pred_elim                         true
% 3.14/1.00  --qbf_split                             512
% 3.14/1.00  
% 3.14/1.00  ------ BMC1 Options
% 3.14/1.00  
% 3.14/1.00  --bmc1_incremental                      false
% 3.14/1.00  --bmc1_axioms                           reachable_all
% 3.14/1.00  --bmc1_min_bound                        0
% 3.14/1.00  --bmc1_max_bound                        -1
% 3.14/1.00  --bmc1_max_bound_default                -1
% 3.14/1.00  --bmc1_symbol_reachability              true
% 3.14/1.00  --bmc1_property_lemmas                  false
% 3.14/1.00  --bmc1_k_induction                      false
% 3.14/1.00  --bmc1_non_equiv_states                 false
% 3.14/1.00  --bmc1_deadlock                         false
% 3.14/1.00  --bmc1_ucm                              false
% 3.14/1.00  --bmc1_add_unsat_core                   none
% 3.14/1.00  --bmc1_unsat_core_children              false
% 3.14/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/1.00  --bmc1_out_stat                         full
% 3.14/1.00  --bmc1_ground_init                      false
% 3.14/1.00  --bmc1_pre_inst_next_state              false
% 3.14/1.00  --bmc1_pre_inst_state                   false
% 3.14/1.00  --bmc1_pre_inst_reach_state             false
% 3.14/1.00  --bmc1_out_unsat_core                   false
% 3.14/1.00  --bmc1_aig_witness_out                  false
% 3.14/1.00  --bmc1_verbose                          false
% 3.14/1.00  --bmc1_dump_clauses_tptp                false
% 3.14/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.14/1.00  --bmc1_dump_file                        -
% 3.14/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.14/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.14/1.00  --bmc1_ucm_extend_mode                  1
% 3.14/1.00  --bmc1_ucm_init_mode                    2
% 3.14/1.00  --bmc1_ucm_cone_mode                    none
% 3.14/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.14/1.00  --bmc1_ucm_relax_model                  4
% 3.14/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.14/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/1.00  --bmc1_ucm_layered_model                none
% 3.14/1.00  --bmc1_ucm_max_lemma_size               10
% 3.14/1.00  
% 3.14/1.00  ------ AIG Options
% 3.14/1.00  
% 3.14/1.00  --aig_mode                              false
% 3.14/1.00  
% 3.14/1.00  ------ Instantiation Options
% 3.14/1.00  
% 3.14/1.00  --instantiation_flag                    true
% 3.14/1.00  --inst_sos_flag                         false
% 3.14/1.00  --inst_sos_phase                        true
% 3.14/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/1.00  --inst_lit_sel_side                     none
% 3.14/1.00  --inst_solver_per_active                1400
% 3.14/1.00  --inst_solver_calls_frac                1.
% 3.14/1.00  --inst_passive_queue_type               priority_queues
% 3.14/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/1.00  --inst_passive_queues_freq              [25;2]
% 3.14/1.00  --inst_dismatching                      true
% 3.14/1.00  --inst_eager_unprocessed_to_passive     true
% 3.14/1.00  --inst_prop_sim_given                   true
% 3.14/1.00  --inst_prop_sim_new                     false
% 3.14/1.00  --inst_subs_new                         false
% 3.14/1.00  --inst_eq_res_simp                      false
% 3.14/1.00  --inst_subs_given                       false
% 3.14/1.00  --inst_orphan_elimination               true
% 3.14/1.00  --inst_learning_loop_flag               true
% 3.14/1.00  --inst_learning_start                   3000
% 3.14/1.00  --inst_learning_factor                  2
% 3.14/1.00  --inst_start_prop_sim_after_learn       3
% 3.14/1.00  --inst_sel_renew                        solver
% 3.14/1.00  --inst_lit_activity_flag                true
% 3.14/1.00  --inst_restr_to_given                   false
% 3.14/1.00  --inst_activity_threshold               500
% 3.14/1.00  --inst_out_proof                        true
% 3.14/1.00  
% 3.14/1.00  ------ Resolution Options
% 3.14/1.00  
% 3.14/1.00  --resolution_flag                       false
% 3.14/1.00  --res_lit_sel                           adaptive
% 3.14/1.00  --res_lit_sel_side                      none
% 3.14/1.00  --res_ordering                          kbo
% 3.14/1.00  --res_to_prop_solver                    active
% 3.14/1.00  --res_prop_simpl_new                    false
% 3.14/1.00  --res_prop_simpl_given                  true
% 3.14/1.00  --res_passive_queue_type                priority_queues
% 3.14/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/1.00  --res_passive_queues_freq               [15;5]
% 3.14/1.00  --res_forward_subs                      full
% 3.14/1.00  --res_backward_subs                     full
% 3.14/1.00  --res_forward_subs_resolution           true
% 3.14/1.00  --res_backward_subs_resolution          true
% 3.14/1.00  --res_orphan_elimination                true
% 3.14/1.00  --res_time_limit                        2.
% 3.14/1.00  --res_out_proof                         true
% 3.14/1.00  
% 3.14/1.00  ------ Superposition Options
% 3.14/1.00  
% 3.14/1.00  --superposition_flag                    true
% 3.14/1.00  --sup_passive_queue_type                priority_queues
% 3.14/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.14/1.00  --demod_completeness_check              fast
% 3.14/1.00  --demod_use_ground                      true
% 3.14/1.00  --sup_to_prop_solver                    passive
% 3.14/1.00  --sup_prop_simpl_new                    true
% 3.14/1.00  --sup_prop_simpl_given                  true
% 3.14/1.00  --sup_fun_splitting                     false
% 3.14/1.00  --sup_smt_interval                      50000
% 3.14/1.00  
% 3.14/1.00  ------ Superposition Simplification Setup
% 3.14/1.00  
% 3.14/1.00  --sup_indices_passive                   []
% 3.14/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_full_bw                           [BwDemod]
% 3.14/1.00  --sup_immed_triv                        [TrivRules]
% 3.14/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_immed_bw_main                     []
% 3.14/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.00  
% 3.14/1.00  ------ Combination Options
% 3.14/1.00  
% 3.14/1.00  --comb_res_mult                         3
% 3.14/1.00  --comb_sup_mult                         2
% 3.14/1.00  --comb_inst_mult                        10
% 3.14/1.00  
% 3.14/1.00  ------ Debug Options
% 3.14/1.00  
% 3.14/1.00  --dbg_backtrace                         false
% 3.14/1.00  --dbg_dump_prop_clauses                 false
% 3.14/1.00  --dbg_dump_prop_clauses_file            -
% 3.14/1.00  --dbg_out_stat                          false
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  ------ Proving...
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  % SZS status Theorem for theBenchmark.p
% 3.14/1.00  
% 3.14/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/1.00  
% 3.14/1.00  fof(f20,conjecture,(
% 3.14/1.00    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f21,negated_conjecture,(
% 3.14/1.00    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.14/1.00    inference(negated_conjecture,[],[f20])).
% 3.14/1.00  
% 3.14/1.00  fof(f25,plain,(
% 3.14/1.00    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 3.14/1.00    inference(ennf_transformation,[],[f21])).
% 3.14/1.00  
% 3.14/1.00  fof(f37,plain,(
% 3.14/1.00    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK3,sK4) = X0) )),
% 3.14/1.00    introduced(choice_axiom,[])).
% 3.14/1.00  
% 3.14/1.00  fof(f36,plain,(
% 3.14/1.00    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 3.14/1.00    introduced(choice_axiom,[])).
% 3.14/1.00  
% 3.14/1.00  fof(f38,plain,(
% 3.14/1.00    (k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & k4_tarski(sK3,sK4) = sK2),
% 3.14/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f37,f36])).
% 3.14/1.00  
% 3.14/1.00  fof(f79,plain,(
% 3.14/1.00    k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2),
% 3.14/1.00    inference(cnf_transformation,[],[f38])).
% 3.14/1.00  
% 3.14/1.00  fof(f78,plain,(
% 3.14/1.00    k4_tarski(sK3,sK4) = sK2),
% 3.14/1.00    inference(cnf_transformation,[],[f38])).
% 3.14/1.00  
% 3.14/1.00  fof(f19,axiom,(
% 3.14/1.00    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f76,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.14/1.00    inference(cnf_transformation,[],[f19])).
% 3.14/1.00  
% 3.14/1.00  fof(f77,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.14/1.00    inference(cnf_transformation,[],[f19])).
% 3.14/1.00  
% 3.14/1.00  fof(f16,axiom,(
% 3.14/1.00    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f57,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f16])).
% 3.14/1.00  
% 3.14/1.00  fof(f5,axiom,(
% 3.14/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f43,plain,(
% 3.14/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f5])).
% 3.14/1.00  
% 3.14/1.00  fof(f88,plain,(
% 3.14/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.14/1.00    inference(definition_unfolding,[],[f43,f84])).
% 3.14/1.00  
% 3.14/1.00  fof(f6,axiom,(
% 3.14/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f44,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f6])).
% 3.14/1.00  
% 3.14/1.00  fof(f7,axiom,(
% 3.14/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f45,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f7])).
% 3.14/1.00  
% 3.14/1.00  fof(f8,axiom,(
% 3.14/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f46,plain,(
% 3.14/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f8])).
% 3.14/1.00  
% 3.14/1.00  fof(f9,axiom,(
% 3.14/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f47,plain,(
% 3.14/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f9])).
% 3.14/1.00  
% 3.14/1.00  fof(f10,axiom,(
% 3.14/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f48,plain,(
% 3.14/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f10])).
% 3.14/1.00  
% 3.14/1.00  fof(f11,axiom,(
% 3.14/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f49,plain,(
% 3.14/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f11])).
% 3.14/1.00  
% 3.14/1.00  fof(f80,plain,(
% 3.14/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.14/1.00    inference(definition_unfolding,[],[f48,f49])).
% 3.14/1.00  
% 3.14/1.00  fof(f81,plain,(
% 3.14/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.14/1.00    inference(definition_unfolding,[],[f47,f80])).
% 3.14/1.00  
% 3.14/1.00  fof(f82,plain,(
% 3.14/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.14/1.00    inference(definition_unfolding,[],[f46,f81])).
% 3.14/1.00  
% 3.14/1.00  fof(f83,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.14/1.00    inference(definition_unfolding,[],[f45,f82])).
% 3.14/1.00  
% 3.14/1.00  fof(f84,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.14/1.00    inference(definition_unfolding,[],[f44,f83])).
% 3.14/1.00  
% 3.14/1.00  fof(f97,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.14/1.00    inference(definition_unfolding,[],[f57,f84,f88,f84])).
% 3.14/1.00  
% 3.14/1.00  fof(f26,plain,(
% 3.14/1.00    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 3.14/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.14/1.00  
% 3.14/1.00  fof(f30,plain,(
% 3.14/1.00    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 3.14/1.00    inference(nnf_transformation,[],[f26])).
% 3.14/1.00  
% 3.14/1.00  fof(f31,plain,(
% 3.14/1.00    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 3.14/1.00    inference(flattening,[],[f30])).
% 3.14/1.00  
% 3.14/1.00  fof(f32,plain,(
% 3.14/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 3.14/1.00    inference(rectify,[],[f31])).
% 3.14/1.00  
% 3.14/1.00  fof(f33,plain,(
% 3.14/1.00    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 3.14/1.00    introduced(choice_axiom,[])).
% 3.14/1.00  
% 3.14/1.00  fof(f34,plain,(
% 3.14/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 3.14/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 3.14/1.00  
% 3.14/1.00  fof(f60,plain,(
% 3.14/1.00    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f34])).
% 3.14/1.00  
% 3.14/1.00  fof(f106,plain,(
% 3.14/1.00    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X0,X1,X2,X3,X4,X8,X6)) )),
% 3.14/1.00    inference(equality_resolution,[],[f60])).
% 3.14/1.00  
% 3.14/1.00  fof(f17,axiom,(
% 3.14/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f24,plain,(
% 3.14/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 3.14/1.00    inference(ennf_transformation,[],[f17])).
% 3.14/1.00  
% 3.14/1.00  fof(f27,plain,(
% 3.14/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 3.14/1.00    inference(definition_folding,[],[f24,f26])).
% 3.14/1.00  
% 3.14/1.00  fof(f35,plain,(
% 3.14/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 3.14/1.00    inference(nnf_transformation,[],[f27])).
% 3.14/1.00  
% 3.14/1.00  fof(f73,plain,(
% 3.14/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 3.14/1.00    inference(cnf_transformation,[],[f35])).
% 3.14/1.00  
% 3.14/1.00  fof(f99,plain,(
% 3.14/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 3.14/1.00    inference(definition_unfolding,[],[f73,f80])).
% 3.14/1.00  
% 3.14/1.00  fof(f107,plain,(
% 3.14/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 3.14/1.00    inference(equality_resolution,[],[f99])).
% 3.14/1.00  
% 3.14/1.00  fof(f15,axiom,(
% 3.14/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f29,plain,(
% 3.14/1.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.14/1.00    inference(nnf_transformation,[],[f15])).
% 3.14/1.00  
% 3.14/1.00  fof(f55,plain,(
% 3.14/1.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f29])).
% 3.14/1.00  
% 3.14/1.00  fof(f2,axiom,(
% 3.14/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f40,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f2])).
% 3.14/1.00  
% 3.14/1.00  fof(f18,axiom,(
% 3.14/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f75,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f18])).
% 3.14/1.00  
% 3.14/1.00  fof(f85,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.14/1.00    inference(definition_unfolding,[],[f75,f84])).
% 3.14/1.00  
% 3.14/1.00  fof(f86,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.14/1.00    inference(definition_unfolding,[],[f40,f85])).
% 3.14/1.00  
% 3.14/1.00  fof(f95,plain,(
% 3.14/1.00    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.14/1.00    inference(definition_unfolding,[],[f55,f86,f88,f88,f88])).
% 3.14/1.00  
% 3.14/1.00  fof(f100,plain,(
% 3.14/1.00    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.14/1.00    inference(equality_resolution,[],[f95])).
% 3.14/1.00  
% 3.14/1.00  fof(f1,axiom,(
% 3.14/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f22,plain,(
% 3.14/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.14/1.00    inference(rectify,[],[f1])).
% 3.14/1.00  
% 3.14/1.00  fof(f39,plain,(
% 3.14/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.14/1.00    inference(cnf_transformation,[],[f22])).
% 3.14/1.00  
% 3.14/1.00  fof(f89,plain,(
% 3.14/1.00    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.14/1.00    inference(definition_unfolding,[],[f39,f85])).
% 3.14/1.00  
% 3.14/1.00  fof(f4,axiom,(
% 3.14/1.00    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f42,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 3.14/1.00    inference(cnf_transformation,[],[f4])).
% 3.14/1.00  
% 3.14/1.00  fof(f13,axiom,(
% 3.14/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f52,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f13])).
% 3.14/1.00  
% 3.14/1.00  fof(f87,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.14/1.00    inference(definition_unfolding,[],[f52,f84])).
% 3.14/1.00  
% 3.14/1.00  fof(f91,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0) )),
% 3.14/1.00    inference(definition_unfolding,[],[f42,f86,f87])).
% 3.14/1.00  
% 3.14/1.00  fof(f3,axiom,(
% 3.14/1.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f41,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.14/1.00    inference(cnf_transformation,[],[f3])).
% 3.14/1.00  
% 3.14/1.00  fof(f90,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0) )),
% 3.14/1.00    inference(definition_unfolding,[],[f41,f85,f87])).
% 3.14/1.00  
% 3.14/1.00  fof(f12,axiom,(
% 3.14/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f28,plain,(
% 3.14/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.14/1.00    inference(nnf_transformation,[],[f12])).
% 3.14/1.00  
% 3.14/1.00  fof(f51,plain,(
% 3.14/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.14/1.00    inference(cnf_transformation,[],[f28])).
% 3.14/1.00  
% 3.14/1.00  fof(f92,plain,(
% 3.14/1.00    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.14/1.00    inference(definition_unfolding,[],[f51,f88])).
% 3.14/1.00  
% 3.14/1.00  fof(f58,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f16])).
% 3.14/1.00  
% 3.14/1.00  fof(f96,plain,(
% 3.14/1.00    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 3.14/1.00    inference(definition_unfolding,[],[f58,f84,f84,f88])).
% 3.14/1.00  
% 3.14/1.00  fof(f14,axiom,(
% 3.14/1.00    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 3.14/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.00  
% 3.14/1.00  fof(f23,plain,(
% 3.14/1.00    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 3.14/1.00    inference(ennf_transformation,[],[f14])).
% 3.14/1.00  
% 3.14/1.00  fof(f54,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f23])).
% 3.14/1.00  
% 3.14/1.00  fof(f53,plain,(
% 3.14/1.00    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 3.14/1.00    inference(cnf_transformation,[],[f23])).
% 3.14/1.00  
% 3.14/1.00  cnf(c_29,negated_conjecture,
% 3.14/1.00      ( k1_mcart_1(sK2) = sK2 | k2_mcart_1(sK2) = sK2 ),
% 3.14/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_30,negated_conjecture,
% 3.14/1.00      ( k4_tarski(sK3,sK4) = sK2 ),
% 3.14/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_28,plain,
% 3.14/1.00      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.14/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3437,plain,
% 3.14/1.00      ( k1_mcart_1(sK2) = sK3 ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_30,c_28]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3448,plain,
% 3.14/1.00      ( k2_mcart_1(sK2) = sK2 | sK3 = sK2 ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_29,c_3437]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_27,plain,
% 3.14/1.00      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.14/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3434,plain,
% 3.14/1.00      ( k2_mcart_1(sK2) = sK4 ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_30,c_27]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3450,plain,
% 3.14/1.00      ( sK4 = sK2 | sK3 = sK2 ),
% 3.14/1.00      inference(demodulation,[status(thm)],[c_3448,c_3434]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3453,plain,
% 3.14/1.00      ( k4_tarski(sK3,sK2) = sK2 | sK3 = sK2 ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_3450,c_30]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_10,plain,
% 3.14/1.00      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 3.14/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3737,plain,
% 3.14/1.00      ( k6_enumset1(k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),k4_tarski(sK3,X0),sK2) = k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_30,c_10]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_4001,plain,
% 3.14/1.00      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.14/1.00      | sK3 = sK2 ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_3453,c_3737]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_23,plain,
% 3.14/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X5,X6) ),
% 3.14/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_26,plain,
% 3.14/1.00      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
% 3.14/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1287,plain,
% 3.14/1.00      ( r2_hidden(X0,X1)
% 3.14/1.00      | X2 != X3
% 3.14/1.00      | X4 != X0
% 3.14/1.00      | X5 != X6
% 3.14/1.00      | X7 != X8
% 3.14/1.00      | X9 != X10
% 3.14/1.00      | X11 != X12
% 3.14/1.00      | k6_enumset1(X4,X4,X4,X5,X7,X9,X11,X2) != X1 ),
% 3.14/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1288,plain,
% 3.14/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
% 3.14/1.00      inference(unflattening,[status(thm)],[c_1287]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1289,plain,
% 3.14/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_1288]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1291,plain,
% 3.14/1.00      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_1289]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_8,plain,
% 3.14/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_0,plain,
% 3.14/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.14/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2,plain,
% 3.14/1.00      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
% 3.14/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1,plain,
% 3.14/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
% 3.14/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3302,plain,
% 3.14/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.14/1.00      inference(light_normalisation,[status(thm)],[c_2,c_1]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3377,plain,
% 3.14/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 3.14/1.00      inference(demodulation,[status(thm)],[c_8,c_0,c_3302]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3385,plain,
% 3.14/1.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_3377]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3,plain,
% 3.14/1.00      ( ~ r2_hidden(X0,X1)
% 3.14/1.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 3.14/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3564,plain,
% 3.14/1.00      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))
% 3.14/1.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3568,plain,
% 3.14/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) != iProver_top
% 3.14/1.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_3564]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3570,plain,
% 3.14/1.00      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 3.14/1.00      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_3568]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_9,plain,
% 3.14/1.00      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 3.14/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3631,plain,
% 3.14/1.00      ( k6_enumset1(k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),sK2) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_30,c_9]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3897,plain,
% 3.14/1.00      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_30,c_3631]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3971,plain,
% 3.14/1.00      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.14/1.00      | sK3 = sK2 ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_3450,c_3897]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5,plain,
% 3.14/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 3.14/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3239,plain,
% 3.14/1.00      ( k1_xboole_0 = X0
% 3.14/1.00      | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_4791,plain,
% 3.14/1.00      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 3.14/1.00      | sK3 = sK2
% 3.14/1.00      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_3971,c_3239]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5826,plain,
% 3.14/1.00      ( sK3 = sK2 ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_4001,c_1291,c_3385,c_3570,c_4791]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_6,plain,
% 3.14/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 3.14/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3238,plain,
% 3.14/1.00      ( k1_xboole_0 = X0
% 3.14/1.00      | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_4550,plain,
% 3.14/1.00      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 3.14/1.00      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_3897,c_3238]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_4993,plain,
% 3.14/1.00      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.14/1.00      inference(forward_subsumption_resolution,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_4550,c_3377]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5832,plain,
% 3.14/1.00      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 3.14/1.00      inference(demodulation,[status(thm)],[c_5826,c_4993]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(contradiction,plain,
% 3.14/1.00      ( $false ),
% 3.14/1.00      inference(minisat,[status(thm)],[c_5832,c_3570,c_1291]) ).
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/1.00  
% 3.14/1.00  ------                               Statistics
% 3.14/1.00  
% 3.14/1.00  ------ General
% 3.14/1.00  
% 3.14/1.00  abstr_ref_over_cycles:                  0
% 3.14/1.00  abstr_ref_under_cycles:                 0
% 3.14/1.00  gc_basic_clause_elim:                   0
% 3.14/1.00  forced_gc_time:                         0
% 3.14/1.00  parsing_time:                           0.011
% 3.14/1.00  unif_index_cands_time:                  0.
% 3.14/1.00  unif_index_add_time:                    0.
% 3.14/1.00  orderings_time:                         0.
% 3.14/1.00  out_proof_time:                         0.008
% 3.14/1.00  total_time:                             0.268
% 3.14/1.00  num_of_symbols:                         47
% 3.14/1.00  num_of_terms:                           8102
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing
% 3.14/1.00  
% 3.14/1.00  num_of_splits:                          0
% 3.14/1.00  num_of_split_atoms:                     0
% 3.14/1.00  num_of_reused_defs:                     0
% 3.14/1.00  num_eq_ax_congr_red:                    28
% 3.14/1.00  num_of_sem_filtered_clauses:            1
% 3.14/1.00  num_of_subtypes:                        0
% 3.14/1.00  monotx_restored_types:                  0
% 3.14/1.00  sat_num_of_epr_types:                   0
% 3.14/1.00  sat_num_of_non_cyclic_types:            0
% 3.14/1.00  sat_guarded_non_collapsed_types:        0
% 3.14/1.00  num_pure_diseq_elim:                    0
% 3.14/1.00  simp_replaced_by:                       0
% 3.14/1.00  res_preprocessed:                       120
% 3.14/1.00  prep_upred:                             0
% 3.14/1.00  prep_unflattend:                        174
% 3.14/1.00  smt_new_axioms:                         0
% 3.14/1.00  pred_elim_cands:                        3
% 3.14/1.00  pred_elim:                              0
% 3.14/1.00  pred_elim_cl:                           0
% 3.14/1.00  pred_elim_cycles:                       3
% 3.14/1.00  merged_defs:                            6
% 3.14/1.00  merged_defs_ncl:                        0
% 3.14/1.00  bin_hyper_res:                          6
% 3.14/1.00  prep_cycles:                            3
% 3.14/1.00  pred_elim_time:                         0.036
% 3.14/1.00  splitting_time:                         0.
% 3.14/1.00  sem_filter_time:                        0.
% 3.14/1.00  monotx_time:                            0.
% 3.14/1.00  subtype_inf_time:                       0.
% 3.14/1.00  
% 3.14/1.00  ------ Problem properties
% 3.14/1.00  
% 3.14/1.00  clauses:                                31
% 3.14/1.00  conjectures:                            2
% 3.14/1.00  epr:                                    7
% 3.14/1.00  horn:                                   27
% 3.14/1.00  ground:                                 2
% 3.14/1.00  unary:                                  10
% 3.14/1.00  binary:                                 13
% 3.14/1.00  lits:                                   70
% 3.14/1.00  lits_eq:                                34
% 3.14/1.00  fd_pure:                                0
% 3.14/1.00  fd_pseudo:                              0
% 3.14/1.00  fd_cond:                                2
% 3.14/1.00  fd_pseudo_cond:                         3
% 3.14/1.00  ac_symbols:                             0
% 3.14/1.00  
% 3.14/1.00  ------ Propositional Solver
% 3.14/1.00  
% 3.14/1.00  prop_solver_calls:                      22
% 3.14/1.00  prop_fast_solver_calls:                 1118
% 3.14/1.00  smt_solver_calls:                       0
% 3.14/1.00  smt_fast_solver_calls:                  0
% 3.14/1.00  prop_num_of_clauses:                    1572
% 3.14/1.00  prop_preprocess_simplified:             6513
% 3.14/1.00  prop_fo_subsumed:                       1
% 3.14/1.00  prop_solver_time:                       0.
% 3.14/1.00  smt_solver_time:                        0.
% 3.14/1.00  smt_fast_solver_time:                   0.
% 3.14/1.00  prop_fast_solver_time:                  0.
% 3.14/1.00  prop_unsat_core_time:                   0.
% 3.14/1.00  
% 3.14/1.00  ------ QBF
% 3.14/1.00  
% 3.14/1.00  qbf_q_res:                              0
% 3.14/1.00  qbf_num_tautologies:                    0
% 3.14/1.00  qbf_prep_cycles:                        0
% 3.14/1.00  
% 3.14/1.00  ------ BMC1
% 3.14/1.00  
% 3.14/1.00  bmc1_current_bound:                     -1
% 3.14/1.00  bmc1_last_solved_bound:                 -1
% 3.14/1.00  bmc1_unsat_core_size:                   -1
% 3.14/1.00  bmc1_unsat_core_parents_size:           -1
% 3.14/1.00  bmc1_merge_next_fun:                    0
% 3.14/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.14/1.00  
% 3.14/1.00  ------ Instantiation
% 3.14/1.00  
% 3.14/1.00  inst_num_of_clauses:                    497
% 3.14/1.00  inst_num_in_passive:                    275
% 3.14/1.00  inst_num_in_active:                     128
% 3.14/1.00  inst_num_in_unprocessed:                94
% 3.14/1.00  inst_num_of_loops:                      170
% 3.14/1.00  inst_num_of_learning_restarts:          0
% 3.14/1.00  inst_num_moves_active_passive:          40
% 3.14/1.00  inst_lit_activity:                      0
% 3.14/1.00  inst_lit_activity_moves:                0
% 3.14/1.00  inst_num_tautologies:                   0
% 3.14/1.00  inst_num_prop_implied:                  0
% 3.14/1.00  inst_num_existing_simplified:           0
% 3.14/1.00  inst_num_eq_res_simplified:             0
% 3.14/1.00  inst_num_child_elim:                    0
% 3.14/1.00  inst_num_of_dismatching_blockings:      138
% 3.14/1.00  inst_num_of_non_proper_insts:           391
% 3.14/1.00  inst_num_of_duplicates:                 0
% 3.14/1.00  inst_inst_num_from_inst_to_res:         0
% 3.14/1.00  inst_dismatching_checking_time:         0.
% 3.14/1.00  
% 3.14/1.00  ------ Resolution
% 3.14/1.00  
% 3.14/1.00  res_num_of_clauses:                     0
% 3.14/1.00  res_num_in_passive:                     0
% 3.14/1.00  res_num_in_active:                      0
% 3.14/1.00  res_num_of_loops:                       123
% 3.14/1.00  res_forward_subset_subsumed:            12
% 3.14/1.00  res_backward_subset_subsumed:           0
% 3.14/1.00  res_forward_subsumed:                   0
% 3.14/1.00  res_backward_subsumed:                  0
% 3.14/1.00  res_forward_subsumption_resolution:     0
% 3.14/1.00  res_backward_subsumption_resolution:    0
% 3.14/1.00  res_clause_to_clause_subsumption:       1615
% 3.14/1.00  res_orphan_elimination:                 0
% 3.14/1.00  res_tautology_del:                      55
% 3.14/1.00  res_num_eq_res_simplified:              0
% 3.14/1.00  res_num_sel_changes:                    0
% 3.14/1.00  res_moves_from_active_to_pass:          0
% 3.14/1.00  
% 3.14/1.00  ------ Superposition
% 3.14/1.00  
% 3.14/1.00  sup_time_total:                         0.
% 3.14/1.00  sup_time_generating:                    0.
% 3.14/1.00  sup_time_sim_full:                      0.
% 3.14/1.00  sup_time_sim_immed:                     0.
% 3.14/1.00  
% 3.14/1.00  sup_num_of_clauses:                     59
% 3.14/1.00  sup_num_in_active:                      16
% 3.14/1.00  sup_num_in_passive:                     43
% 3.14/1.00  sup_num_of_loops:                       32
% 3.14/1.00  sup_fw_superposition:                   194
% 3.14/1.00  sup_bw_superposition:                   13
% 3.14/1.00  sup_immediate_simplified:               9
% 3.14/1.00  sup_given_eliminated:                   0
% 3.14/1.00  comparisons_done:                       0
% 3.14/1.00  comparisons_avoided:                    8
% 3.14/1.00  
% 3.14/1.00  ------ Simplifications
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  sim_fw_subset_subsumed:                 2
% 3.14/1.00  sim_bw_subset_subsumed:                 2
% 3.14/1.00  sim_fw_subsumed:                        4
% 3.14/1.00  sim_bw_subsumed:                        0
% 3.14/1.00  sim_fw_subsumption_res:                 4
% 3.14/1.00  sim_bw_subsumption_res:                 0
% 3.14/1.00  sim_tautology_del:                      0
% 3.14/1.00  sim_eq_tautology_del:                   5
% 3.14/1.00  sim_eq_res_simp:                        0
% 3.14/1.00  sim_fw_demodulated:                     3
% 3.14/1.00  sim_bw_demodulated:                     16
% 3.14/1.00  sim_light_normalised:                   5
% 3.14/1.00  sim_joinable_taut:                      0
% 3.14/1.00  sim_joinable_simp:                      0
% 3.14/1.00  sim_ac_normalised:                      0
% 3.14/1.00  sim_smt_subsumption:                    0
% 3.14/1.00  
%------------------------------------------------------------------------------
