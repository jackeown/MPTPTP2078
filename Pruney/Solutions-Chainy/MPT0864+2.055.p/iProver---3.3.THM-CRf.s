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
% DateTime   : Thu Dec  3 11:57:56 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  140 (1136 expanded)
%              Number of clauses        :   55 ( 146 expanded)
%              Number of leaves         :   24 ( 336 expanded)
%              Depth                    :   19
%              Number of atoms          :  412 (3048 expanded)
%              Number of equality atoms :  313 (2451 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP0(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f24,f26])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f76,f83])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f100])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X0,X1,X2,X3,X4,X8,X6) ) ),
    inference(equality_resolution,[],[f63])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X0 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    ! [X6,X4,X2,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X8,X1,X2,X3,X4,X5,X6) ) ),
    inference(equality_resolution,[],[f68])).

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

fof(f39,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK3,sK4) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK2) = sK2
        | k1_mcart_1(sK2) = sK2 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK2 ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k2_mcart_1(sK2) = sK2
      | k1_mcart_1(sK2) = sK2 )
    & k4_tarski(sK3,sK4) = sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f39,f38])).

fof(f82,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f83])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f84])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f85])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f86])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f87])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f91])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f87])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f88])).

fof(f98,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f60,f89,f91,f91,f91])).

fof(f101,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f92,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f88])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f87])).

fof(f94,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f44,f89,f90])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f93,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f43,f88,f90])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_27,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2192,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X5,X6) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2195,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6) != iProver_top
    | r2_hidden(X5,X6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4357,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2192,c_2195])).

cnf(c_19,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X0,X6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2200,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6) != iProver_top
    | r2_hidden(X0,X6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4352,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2192,c_2200])).

cnf(c_30,negated_conjecture,
    ( k1_mcart_1(sK2) = sK2
    | k2_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,negated_conjecture,
    ( k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2426,plain,
    ( k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_31,c_29])).

cnf(c_2437,plain,
    ( k2_mcart_1(sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_30,c_2426])).

cnf(c_28,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2423,plain,
    ( k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_31,c_28])).

cnf(c_2439,plain,
    ( sK4 = sK2
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_2437,c_2423])).

cnf(c_2442,plain,
    ( k4_tarski(sK3,sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_2439,c_31])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2212,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4017,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,X0) != iProver_top
    | r2_hidden(sK2,X1) != iProver_top
    | r2_hidden(sK2,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2442,c_2212])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2211,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3491,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK2,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_2211])).

cnf(c_4249,plain,
    ( sK3 = sK2
    | r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK3,X1) != iProver_top
    | r2_hidden(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4017,c_3491])).

cnf(c_4530,plain,
    ( sK3 = sK2
    | r2_hidden(sK4,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,sK2)) = iProver_top
    | r2_hidden(sK3,X5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4352,c_4249])).

cnf(c_4595,plain,
    ( sK3 = sK2
    | r2_hidden(sK4,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4352,c_4530])).

cnf(c_4016,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r2_hidden(sK3,X1) != iProver_top
    | r2_hidden(sK2,k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_2212])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2214,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2209,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4388,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2214,c_2209])).

cnf(c_11,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2289,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_1])).

cnf(c_2360,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11,c_0,c_2289])).

cnf(c_5745,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4388,c_2360])).

cnf(c_5754,plain,
    ( r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4016,c_5745])).

cnf(c_5936,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4595,c_5754])).

cnf(c_6809,plain,
    ( sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_4357,c_5936])).

cnf(c_6943,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r2_hidden(sK2,X1) != iProver_top
    | r2_hidden(sK2,k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6809,c_4016])).

cnf(c_1318,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | X11 != X12
    | k6_enumset1(X4,X4,X4,X5,X7,X9,X11,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_1319,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(unflattening,[status(thm)],[c_1318])).

cnf(c_1320,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_1322,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2208,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4389,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2214,c_2208])).

cnf(c_5950,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4389,c_2360])).

cnf(c_5958,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4016,c_5950])).

cnf(c_6941,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6809,c_5958])).

cnf(c_7709,plain,
    ( r2_hidden(sK4,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6943,c_1322,c_6941])).

cnf(c_7716,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4357,c_7709])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.01/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.00  
% 4.01/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/1.00  
% 4.01/1.00  ------  iProver source info
% 4.01/1.00  
% 4.01/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.01/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/1.00  git: non_committed_changes: false
% 4.01/1.00  git: last_make_outside_of_git: false
% 4.01/1.00  
% 4.01/1.00  ------ 
% 4.01/1.00  
% 4.01/1.00  ------ Input Options
% 4.01/1.00  
% 4.01/1.00  --out_options                           all
% 4.01/1.00  --tptp_safe_out                         true
% 4.01/1.00  --problem_path                          ""
% 4.01/1.00  --include_path                          ""
% 4.01/1.00  --clausifier                            res/vclausify_rel
% 4.01/1.00  --clausifier_options                    --mode clausify
% 4.01/1.00  --stdin                                 false
% 4.01/1.00  --stats_out                             all
% 4.01/1.00  
% 4.01/1.00  ------ General Options
% 4.01/1.00  
% 4.01/1.00  --fof                                   false
% 4.01/1.00  --time_out_real                         305.
% 4.01/1.00  --time_out_virtual                      -1.
% 4.01/1.00  --symbol_type_check                     false
% 4.01/1.00  --clausify_out                          false
% 4.01/1.00  --sig_cnt_out                           false
% 4.01/1.00  --trig_cnt_out                          false
% 4.01/1.00  --trig_cnt_out_tolerance                1.
% 4.01/1.00  --trig_cnt_out_sk_spl                   false
% 4.01/1.00  --abstr_cl_out                          false
% 4.01/1.00  
% 4.01/1.00  ------ Global Options
% 4.01/1.00  
% 4.01/1.00  --schedule                              default
% 4.01/1.00  --add_important_lit                     false
% 4.01/1.00  --prop_solver_per_cl                    1000
% 4.01/1.00  --min_unsat_core                        false
% 4.01/1.00  --soft_assumptions                      false
% 4.01/1.00  --soft_lemma_size                       3
% 4.01/1.00  --prop_impl_unit_size                   0
% 4.01/1.00  --prop_impl_unit                        []
% 4.01/1.00  --share_sel_clauses                     true
% 4.01/1.00  --reset_solvers                         false
% 4.01/1.00  --bc_imp_inh                            [conj_cone]
% 4.01/1.00  --conj_cone_tolerance                   3.
% 4.01/1.00  --extra_neg_conj                        none
% 4.01/1.00  --large_theory_mode                     true
% 4.01/1.00  --prolific_symb_bound                   200
% 4.01/1.00  --lt_threshold                          2000
% 4.01/1.00  --clause_weak_htbl                      true
% 4.01/1.00  --gc_record_bc_elim                     false
% 4.01/1.00  
% 4.01/1.00  ------ Preprocessing Options
% 4.01/1.00  
% 4.01/1.00  --preprocessing_flag                    true
% 4.01/1.00  --time_out_prep_mult                    0.1
% 4.01/1.00  --splitting_mode                        input
% 4.01/1.00  --splitting_grd                         true
% 4.01/1.00  --splitting_cvd                         false
% 4.01/1.00  --splitting_cvd_svl                     false
% 4.01/1.00  --splitting_nvd                         32
% 4.01/1.00  --sub_typing                            true
% 4.01/1.00  --prep_gs_sim                           true
% 4.01/1.00  --prep_unflatten                        true
% 4.01/1.00  --prep_res_sim                          true
% 4.01/1.00  --prep_upred                            true
% 4.01/1.00  --prep_sem_filter                       exhaustive
% 4.01/1.00  --prep_sem_filter_out                   false
% 4.01/1.00  --pred_elim                             true
% 4.01/1.00  --res_sim_input                         true
% 4.01/1.00  --eq_ax_congr_red                       true
% 4.01/1.00  --pure_diseq_elim                       true
% 4.01/1.00  --brand_transform                       false
% 4.01/1.00  --non_eq_to_eq                          false
% 4.01/1.00  --prep_def_merge                        true
% 4.01/1.00  --prep_def_merge_prop_impl              false
% 4.01/1.00  --prep_def_merge_mbd                    true
% 4.01/1.00  --prep_def_merge_tr_red                 false
% 4.01/1.00  --prep_def_merge_tr_cl                  false
% 4.01/1.00  --smt_preprocessing                     true
% 4.01/1.00  --smt_ac_axioms                         fast
% 4.01/1.00  --preprocessed_out                      false
% 4.01/1.00  --preprocessed_stats                    false
% 4.01/1.00  
% 4.01/1.00  ------ Abstraction refinement Options
% 4.01/1.00  
% 4.01/1.00  --abstr_ref                             []
% 4.01/1.00  --abstr_ref_prep                        false
% 4.01/1.00  --abstr_ref_until_sat                   false
% 4.01/1.00  --abstr_ref_sig_restrict                funpre
% 4.01/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/1.00  --abstr_ref_under                       []
% 4.01/1.00  
% 4.01/1.00  ------ SAT Options
% 4.01/1.00  
% 4.01/1.00  --sat_mode                              false
% 4.01/1.00  --sat_fm_restart_options                ""
% 4.01/1.00  --sat_gr_def                            false
% 4.01/1.00  --sat_epr_types                         true
% 4.01/1.00  --sat_non_cyclic_types                  false
% 4.01/1.00  --sat_finite_models                     false
% 4.01/1.00  --sat_fm_lemmas                         false
% 4.01/1.00  --sat_fm_prep                           false
% 4.01/1.00  --sat_fm_uc_incr                        true
% 4.01/1.00  --sat_out_model                         small
% 4.01/1.00  --sat_out_clauses                       false
% 4.01/1.00  
% 4.01/1.00  ------ QBF Options
% 4.01/1.00  
% 4.01/1.00  --qbf_mode                              false
% 4.01/1.00  --qbf_elim_univ                         false
% 4.01/1.00  --qbf_dom_inst                          none
% 4.01/1.00  --qbf_dom_pre_inst                      false
% 4.01/1.00  --qbf_sk_in                             false
% 4.01/1.00  --qbf_pred_elim                         true
% 4.01/1.00  --qbf_split                             512
% 4.01/1.00  
% 4.01/1.00  ------ BMC1 Options
% 4.01/1.00  
% 4.01/1.00  --bmc1_incremental                      false
% 4.01/1.00  --bmc1_axioms                           reachable_all
% 4.01/1.00  --bmc1_min_bound                        0
% 4.01/1.00  --bmc1_max_bound                        -1
% 4.01/1.00  --bmc1_max_bound_default                -1
% 4.01/1.00  --bmc1_symbol_reachability              true
% 4.01/1.00  --bmc1_property_lemmas                  false
% 4.01/1.00  --bmc1_k_induction                      false
% 4.01/1.00  --bmc1_non_equiv_states                 false
% 4.01/1.00  --bmc1_deadlock                         false
% 4.01/1.00  --bmc1_ucm                              false
% 4.01/1.00  --bmc1_add_unsat_core                   none
% 4.01/1.00  --bmc1_unsat_core_children              false
% 4.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/1.00  --bmc1_out_stat                         full
% 4.01/1.00  --bmc1_ground_init                      false
% 4.01/1.00  --bmc1_pre_inst_next_state              false
% 4.01/1.00  --bmc1_pre_inst_state                   false
% 4.01/1.00  --bmc1_pre_inst_reach_state             false
% 4.01/1.00  --bmc1_out_unsat_core                   false
% 4.01/1.00  --bmc1_aig_witness_out                  false
% 4.01/1.00  --bmc1_verbose                          false
% 4.01/1.00  --bmc1_dump_clauses_tptp                false
% 4.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.01/1.00  --bmc1_dump_file                        -
% 4.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.01/1.00  --bmc1_ucm_extend_mode                  1
% 4.01/1.00  --bmc1_ucm_init_mode                    2
% 4.01/1.00  --bmc1_ucm_cone_mode                    none
% 4.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.01/1.00  --bmc1_ucm_relax_model                  4
% 4.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/1.00  --bmc1_ucm_layered_model                none
% 4.01/1.00  --bmc1_ucm_max_lemma_size               10
% 4.01/1.00  
% 4.01/1.00  ------ AIG Options
% 4.01/1.00  
% 4.01/1.00  --aig_mode                              false
% 4.01/1.00  
% 4.01/1.00  ------ Instantiation Options
% 4.01/1.00  
% 4.01/1.00  --instantiation_flag                    true
% 4.01/1.00  --inst_sos_flag                         false
% 4.01/1.00  --inst_sos_phase                        true
% 4.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/1.00  --inst_lit_sel_side                     num_symb
% 4.01/1.00  --inst_solver_per_active                1400
% 4.01/1.00  --inst_solver_calls_frac                1.
% 4.01/1.00  --inst_passive_queue_type               priority_queues
% 4.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/1.00  --inst_passive_queues_freq              [25;2]
% 4.01/1.00  --inst_dismatching                      true
% 4.01/1.00  --inst_eager_unprocessed_to_passive     true
% 4.01/1.00  --inst_prop_sim_given                   true
% 4.01/1.00  --inst_prop_sim_new                     false
% 4.01/1.00  --inst_subs_new                         false
% 4.01/1.00  --inst_eq_res_simp                      false
% 4.01/1.00  --inst_subs_given                       false
% 4.01/1.00  --inst_orphan_elimination               true
% 4.01/1.00  --inst_learning_loop_flag               true
% 4.01/1.00  --inst_learning_start                   3000
% 4.01/1.00  --inst_learning_factor                  2
% 4.01/1.00  --inst_start_prop_sim_after_learn       3
% 4.01/1.00  --inst_sel_renew                        solver
% 4.01/1.00  --inst_lit_activity_flag                true
% 4.01/1.00  --inst_restr_to_given                   false
% 4.01/1.00  --inst_activity_threshold               500
% 4.01/1.00  --inst_out_proof                        true
% 4.01/1.00  
% 4.01/1.00  ------ Resolution Options
% 4.01/1.00  
% 4.01/1.00  --resolution_flag                       true
% 4.01/1.00  --res_lit_sel                           adaptive
% 4.01/1.00  --res_lit_sel_side                      none
% 4.01/1.00  --res_ordering                          kbo
% 4.01/1.00  --res_to_prop_solver                    active
% 4.01/1.00  --res_prop_simpl_new                    false
% 4.01/1.00  --res_prop_simpl_given                  true
% 4.01/1.00  --res_passive_queue_type                priority_queues
% 4.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/1.00  --res_passive_queues_freq               [15;5]
% 4.01/1.00  --res_forward_subs                      full
% 4.01/1.00  --res_backward_subs                     full
% 4.01/1.00  --res_forward_subs_resolution           true
% 4.01/1.00  --res_backward_subs_resolution          true
% 4.01/1.00  --res_orphan_elimination                true
% 4.01/1.00  --res_time_limit                        2.
% 4.01/1.00  --res_out_proof                         true
% 4.01/1.00  
% 4.01/1.00  ------ Superposition Options
% 4.01/1.00  
% 4.01/1.00  --superposition_flag                    true
% 4.01/1.00  --sup_passive_queue_type                priority_queues
% 4.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.01/1.00  --demod_completeness_check              fast
% 4.01/1.00  --demod_use_ground                      true
% 4.01/1.00  --sup_to_prop_solver                    passive
% 4.01/1.00  --sup_prop_simpl_new                    true
% 4.01/1.00  --sup_prop_simpl_given                  true
% 4.01/1.00  --sup_fun_splitting                     false
% 4.01/1.00  --sup_smt_interval                      50000
% 4.01/1.00  
% 4.01/1.00  ------ Superposition Simplification Setup
% 4.01/1.00  
% 4.01/1.00  --sup_indices_passive                   []
% 4.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/1.00  --sup_full_bw                           [BwDemod]
% 4.01/1.00  --sup_immed_triv                        [TrivRules]
% 4.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/1.00  --sup_immed_bw_main                     []
% 4.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/1.00  
% 4.01/1.00  ------ Combination Options
% 4.01/1.00  
% 4.01/1.00  --comb_res_mult                         3
% 4.01/1.00  --comb_sup_mult                         2
% 4.01/1.00  --comb_inst_mult                        10
% 4.01/1.00  
% 4.01/1.00  ------ Debug Options
% 4.01/1.00  
% 4.01/1.00  --dbg_backtrace                         false
% 4.01/1.00  --dbg_dump_prop_clauses                 false
% 4.01/1.00  --dbg_dump_prop_clauses_file            -
% 4.01/1.00  --dbg_out_stat                          false
% 4.01/1.00  ------ Parsing...
% 4.01/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/1.00  
% 4.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.01/1.00  
% 4.01/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/1.00  
% 4.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/1.00  ------ Proving...
% 4.01/1.00  ------ Problem Properties 
% 4.01/1.00  
% 4.01/1.00  
% 4.01/1.00  clauses                                 32
% 4.01/1.00  conjectures                             2
% 4.01/1.00  EPR                                     7
% 4.01/1.00  Horn                                    28
% 4.01/1.00  unary                                   8
% 4.01/1.00  binary                                  15
% 4.01/1.00  lits                                    75
% 4.01/1.00  lits eq                                 32
% 4.01/1.00  fd_pure                                 0
% 4.01/1.00  fd_pseudo                               0
% 4.01/1.00  fd_cond                                 2
% 4.01/1.00  fd_pseudo_cond                          3
% 4.01/1.00  AC symbols                              0
% 4.01/1.00  
% 4.01/1.00  ------ Schedule dynamic 5 is on 
% 4.01/1.00  
% 4.01/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.01/1.00  
% 4.01/1.00  
% 4.01/1.00  ------ 
% 4.01/1.00  Current options:
% 4.01/1.00  ------ 
% 4.01/1.00  
% 4.01/1.00  ------ Input Options
% 4.01/1.00  
% 4.01/1.00  --out_options                           all
% 4.01/1.00  --tptp_safe_out                         true
% 4.01/1.00  --problem_path                          ""
% 4.01/1.00  --include_path                          ""
% 4.01/1.00  --clausifier                            res/vclausify_rel
% 4.01/1.00  --clausifier_options                    --mode clausify
% 4.01/1.00  --stdin                                 false
% 4.01/1.00  --stats_out                             all
% 4.01/1.00  
% 4.01/1.00  ------ General Options
% 4.01/1.00  
% 4.01/1.00  --fof                                   false
% 4.01/1.00  --time_out_real                         305.
% 4.01/1.00  --time_out_virtual                      -1.
% 4.01/1.00  --symbol_type_check                     false
% 4.01/1.00  --clausify_out                          false
% 4.01/1.00  --sig_cnt_out                           false
% 4.01/1.00  --trig_cnt_out                          false
% 4.01/1.00  --trig_cnt_out_tolerance                1.
% 4.01/1.00  --trig_cnt_out_sk_spl                   false
% 4.01/1.00  --abstr_cl_out                          false
% 4.01/1.00  
% 4.01/1.00  ------ Global Options
% 4.01/1.00  
% 4.01/1.00  --schedule                              default
% 4.01/1.00  --add_important_lit                     false
% 4.01/1.00  --prop_solver_per_cl                    1000
% 4.01/1.00  --min_unsat_core                        false
% 4.01/1.00  --soft_assumptions                      false
% 4.01/1.00  --soft_lemma_size                       3
% 4.01/1.00  --prop_impl_unit_size                   0
% 4.01/1.00  --prop_impl_unit                        []
% 4.01/1.00  --share_sel_clauses                     true
% 4.01/1.00  --reset_solvers                         false
% 4.01/1.00  --bc_imp_inh                            [conj_cone]
% 4.01/1.00  --conj_cone_tolerance                   3.
% 4.01/1.00  --extra_neg_conj                        none
% 4.01/1.00  --large_theory_mode                     true
% 4.01/1.00  --prolific_symb_bound                   200
% 4.01/1.00  --lt_threshold                          2000
% 4.01/1.00  --clause_weak_htbl                      true
% 4.01/1.00  --gc_record_bc_elim                     false
% 4.01/1.00  
% 4.01/1.00  ------ Preprocessing Options
% 4.01/1.00  
% 4.01/1.00  --preprocessing_flag                    true
% 4.01/1.00  --time_out_prep_mult                    0.1
% 4.01/1.00  --splitting_mode                        input
% 4.01/1.00  --splitting_grd                         true
% 4.01/1.00  --splitting_cvd                         false
% 4.01/1.00  --splitting_cvd_svl                     false
% 4.01/1.00  --splitting_nvd                         32
% 4.01/1.00  --sub_typing                            true
% 4.01/1.00  --prep_gs_sim                           true
% 4.01/1.00  --prep_unflatten                        true
% 4.01/1.00  --prep_res_sim                          true
% 4.01/1.00  --prep_upred                            true
% 4.01/1.00  --prep_sem_filter                       exhaustive
% 4.01/1.00  --prep_sem_filter_out                   false
% 4.01/1.00  --pred_elim                             true
% 4.01/1.00  --res_sim_input                         true
% 4.01/1.00  --eq_ax_congr_red                       true
% 4.01/1.00  --pure_diseq_elim                       true
% 4.01/1.00  --brand_transform                       false
% 4.01/1.00  --non_eq_to_eq                          false
% 4.01/1.00  --prep_def_merge                        true
% 4.01/1.00  --prep_def_merge_prop_impl              false
% 4.01/1.00  --prep_def_merge_mbd                    true
% 4.01/1.00  --prep_def_merge_tr_red                 false
% 4.01/1.00  --prep_def_merge_tr_cl                  false
% 4.01/1.00  --smt_preprocessing                     true
% 4.01/1.00  --smt_ac_axioms                         fast
% 4.01/1.00  --preprocessed_out                      false
% 4.01/1.00  --preprocessed_stats                    false
% 4.01/1.00  
% 4.01/1.00  ------ Abstraction refinement Options
% 4.01/1.00  
% 4.01/1.00  --abstr_ref                             []
% 4.01/1.00  --abstr_ref_prep                        false
% 4.01/1.00  --abstr_ref_until_sat                   false
% 4.01/1.00  --abstr_ref_sig_restrict                funpre
% 4.01/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/1.00  --abstr_ref_under                       []
% 4.01/1.00  
% 4.01/1.00  ------ SAT Options
% 4.01/1.00  
% 4.01/1.00  --sat_mode                              false
% 4.01/1.00  --sat_fm_restart_options                ""
% 4.01/1.00  --sat_gr_def                            false
% 4.01/1.00  --sat_epr_types                         true
% 4.01/1.00  --sat_non_cyclic_types                  false
% 4.01/1.00  --sat_finite_models                     false
% 4.01/1.00  --sat_fm_lemmas                         false
% 4.01/1.00  --sat_fm_prep                           false
% 4.01/1.00  --sat_fm_uc_incr                        true
% 4.01/1.00  --sat_out_model                         small
% 4.01/1.00  --sat_out_clauses                       false
% 4.01/1.00  
% 4.01/1.00  ------ QBF Options
% 4.01/1.00  
% 4.01/1.00  --qbf_mode                              false
% 4.01/1.00  --qbf_elim_univ                         false
% 4.01/1.00  --qbf_dom_inst                          none
% 4.01/1.00  --qbf_dom_pre_inst                      false
% 4.01/1.00  --qbf_sk_in                             false
% 4.01/1.00  --qbf_pred_elim                         true
% 4.01/1.00  --qbf_split                             512
% 4.01/1.00  
% 4.01/1.00  ------ BMC1 Options
% 4.01/1.00  
% 4.01/1.00  --bmc1_incremental                      false
% 4.01/1.00  --bmc1_axioms                           reachable_all
% 4.01/1.00  --bmc1_min_bound                        0
% 4.01/1.00  --bmc1_max_bound                        -1
% 4.01/1.00  --bmc1_max_bound_default                -1
% 4.01/1.00  --bmc1_symbol_reachability              true
% 4.01/1.00  --bmc1_property_lemmas                  false
% 4.01/1.00  --bmc1_k_induction                      false
% 4.01/1.00  --bmc1_non_equiv_states                 false
% 4.01/1.00  --bmc1_deadlock                         false
% 4.01/1.00  --bmc1_ucm                              false
% 4.01/1.00  --bmc1_add_unsat_core                   none
% 4.01/1.00  --bmc1_unsat_core_children              false
% 4.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/1.00  --bmc1_out_stat                         full
% 4.01/1.00  --bmc1_ground_init                      false
% 4.01/1.00  --bmc1_pre_inst_next_state              false
% 4.01/1.00  --bmc1_pre_inst_state                   false
% 4.01/1.00  --bmc1_pre_inst_reach_state             false
% 4.01/1.00  --bmc1_out_unsat_core                   false
% 4.01/1.00  --bmc1_aig_witness_out                  false
% 4.01/1.00  --bmc1_verbose                          false
% 4.01/1.00  --bmc1_dump_clauses_tptp                false
% 4.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.01/1.00  --bmc1_dump_file                        -
% 4.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.01/1.00  --bmc1_ucm_extend_mode                  1
% 4.01/1.00  --bmc1_ucm_init_mode                    2
% 4.01/1.00  --bmc1_ucm_cone_mode                    none
% 4.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.01/1.00  --bmc1_ucm_relax_model                  4
% 4.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/1.00  --bmc1_ucm_layered_model                none
% 4.01/1.00  --bmc1_ucm_max_lemma_size               10
% 4.01/1.00  
% 4.01/1.00  ------ AIG Options
% 4.01/1.00  
% 4.01/1.00  --aig_mode                              false
% 4.01/1.00  
% 4.01/1.00  ------ Instantiation Options
% 4.01/1.00  
% 4.01/1.00  --instantiation_flag                    true
% 4.01/1.00  --inst_sos_flag                         false
% 4.01/1.00  --inst_sos_phase                        true
% 4.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/1.00  --inst_lit_sel_side                     none
% 4.01/1.00  --inst_solver_per_active                1400
% 4.01/1.00  --inst_solver_calls_frac                1.
% 4.01/1.00  --inst_passive_queue_type               priority_queues
% 4.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/1.00  --inst_passive_queues_freq              [25;2]
% 4.01/1.00  --inst_dismatching                      true
% 4.01/1.00  --inst_eager_unprocessed_to_passive     true
% 4.01/1.00  --inst_prop_sim_given                   true
% 4.01/1.00  --inst_prop_sim_new                     false
% 4.01/1.00  --inst_subs_new                         false
% 4.01/1.00  --inst_eq_res_simp                      false
% 4.01/1.00  --inst_subs_given                       false
% 4.01/1.00  --inst_orphan_elimination               true
% 4.01/1.00  --inst_learning_loop_flag               true
% 4.01/1.00  --inst_learning_start                   3000
% 4.01/1.00  --inst_learning_factor                  2
% 4.01/1.00  --inst_start_prop_sim_after_learn       3
% 4.01/1.00  --inst_sel_renew                        solver
% 4.01/1.00  --inst_lit_activity_flag                true
% 4.01/1.00  --inst_restr_to_given                   false
% 4.01/1.00  --inst_activity_threshold               500
% 4.01/1.00  --inst_out_proof                        true
% 4.01/1.00  
% 4.01/1.00  ------ Resolution Options
% 4.01/1.00  
% 4.01/1.00  --resolution_flag                       false
% 4.01/1.00  --res_lit_sel                           adaptive
% 4.01/1.00  --res_lit_sel_side                      none
% 4.01/1.00  --res_ordering                          kbo
% 4.01/1.00  --res_to_prop_solver                    active
% 4.01/1.00  --res_prop_simpl_new                    false
% 4.01/1.00  --res_prop_simpl_given                  true
% 4.01/1.00  --res_passive_queue_type                priority_queues
% 4.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/1.00  --res_passive_queues_freq               [15;5]
% 4.01/1.00  --res_forward_subs                      full
% 4.01/1.00  --res_backward_subs                     full
% 4.01/1.00  --res_forward_subs_resolution           true
% 4.01/1.00  --res_backward_subs_resolution          true
% 4.01/1.00  --res_orphan_elimination                true
% 4.01/1.00  --res_time_limit                        2.
% 4.01/1.00  --res_out_proof                         true
% 4.01/1.00  
% 4.01/1.00  ------ Superposition Options
% 4.01/1.00  
% 4.01/1.00  --superposition_flag                    true
% 4.01/1.00  --sup_passive_queue_type                priority_queues
% 4.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.01/1.00  --demod_completeness_check              fast
% 4.01/1.00  --demod_use_ground                      true
% 4.01/1.00  --sup_to_prop_solver                    passive
% 4.01/1.00  --sup_prop_simpl_new                    true
% 4.01/1.00  --sup_prop_simpl_given                  true
% 4.01/1.00  --sup_fun_splitting                     false
% 4.01/1.00  --sup_smt_interval                      50000
% 4.01/1.00  
% 4.01/1.00  ------ Superposition Simplification Setup
% 4.01/1.00  
% 4.01/1.00  --sup_indices_passive                   []
% 4.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/1.00  --sup_full_bw                           [BwDemod]
% 4.01/1.00  --sup_immed_triv                        [TrivRules]
% 4.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/1.00  --sup_immed_bw_main                     []
% 4.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/1.00  
% 4.01/1.00  ------ Combination Options
% 4.01/1.00  
% 4.01/1.00  --comb_res_mult                         3
% 4.01/1.00  --comb_sup_mult                         2
% 4.01/1.00  --comb_inst_mult                        10
% 4.01/1.00  
% 4.01/1.00  ------ Debug Options
% 4.01/1.00  
% 4.01/1.00  --dbg_backtrace                         false
% 4.01/1.00  --dbg_dump_prop_clauses                 false
% 4.01/1.00  --dbg_dump_prop_clauses_file            -
% 4.01/1.00  --dbg_out_stat                          false
% 4.01/1.00  
% 4.01/1.00  
% 4.01/1.00  
% 4.01/1.00  
% 4.01/1.00  ------ Proving...
% 4.01/1.00  
% 4.01/1.00  
% 4.01/1.00  % SZS status Theorem for theBenchmark.p
% 4.01/1.00  
% 4.01/1.00   Resolution empty clause
% 4.01/1.00  
% 4.01/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/1.00  
% 4.01/1.00  fof(f17,axiom,(
% 4.01/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f24,plain,(
% 4.01/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 4.01/1.00    inference(ennf_transformation,[],[f17])).
% 4.01/1.00  
% 4.01/1.00  fof(f26,plain,(
% 4.01/1.00    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 4.01/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.01/1.00  
% 4.01/1.00  fof(f27,plain,(
% 4.01/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 4.01/1.00    inference(definition_folding,[],[f24,f26])).
% 4.01/1.00  
% 4.01/1.00  fof(f37,plain,(
% 4.01/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 4.01/1.00    inference(nnf_transformation,[],[f27])).
% 4.01/1.00  
% 4.01/1.00  fof(f76,plain,(
% 4.01/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 4.01/1.00    inference(cnf_transformation,[],[f37])).
% 4.01/1.00  
% 4.01/1.00  fof(f10,axiom,(
% 4.01/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f50,plain,(
% 4.01/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f10])).
% 4.01/1.00  
% 4.01/1.00  fof(f11,axiom,(
% 4.01/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f51,plain,(
% 4.01/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f11])).
% 4.01/1.00  
% 4.01/1.00  fof(f83,plain,(
% 4.01/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.01/1.00    inference(definition_unfolding,[],[f50,f51])).
% 4.01/1.00  
% 4.01/1.00  fof(f100,plain,(
% 4.01/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 4.01/1.00    inference(definition_unfolding,[],[f76,f83])).
% 4.01/1.00  
% 4.01/1.00  fof(f108,plain,(
% 4.01/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 4.01/1.00    inference(equality_resolution,[],[f100])).
% 4.01/1.00  
% 4.01/1.00  fof(f32,plain,(
% 4.01/1.00    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 4.01/1.00    inference(nnf_transformation,[],[f26])).
% 4.01/1.00  
% 4.01/1.00  fof(f33,plain,(
% 4.01/1.00    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 4.01/1.00    inference(flattening,[],[f32])).
% 4.01/1.00  
% 4.01/1.00  fof(f34,plain,(
% 4.01/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 4.01/1.00    inference(rectify,[],[f33])).
% 4.01/1.00  
% 4.01/1.00  fof(f35,plain,(
% 4.01/1.00    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 4.01/1.00    introduced(choice_axiom,[])).
% 4.01/1.00  
% 4.01/1.00  fof(f36,plain,(
% 4.01/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 4.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 4.01/1.00  
% 4.01/1.00  fof(f63,plain,(
% 4.01/1.00    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f36])).
% 4.01/1.00  
% 4.01/1.00  fof(f107,plain,(
% 4.01/1.00    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X0,X1,X2,X3,X4,X8,X6)) )),
% 4.01/1.00    inference(equality_resolution,[],[f63])).
% 4.01/1.00  
% 4.01/1.00  fof(f68,plain,(
% 4.01/1.00    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X0 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f36])).
% 4.01/1.00  
% 4.01/1.00  fof(f102,plain,(
% 4.01/1.00    ( ! [X6,X4,X2,X8,X5,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X8,X1,X2,X3,X4,X5,X6)) )),
% 4.01/1.00    inference(equality_resolution,[],[f68])).
% 4.01/1.00  
% 4.01/1.00  fof(f20,conjecture,(
% 4.01/1.00    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f21,negated_conjecture,(
% 4.01/1.00    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 4.01/1.00    inference(negated_conjecture,[],[f20])).
% 4.01/1.00  
% 4.01/1.00  fof(f25,plain,(
% 4.01/1.00    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 4.01/1.00    inference(ennf_transformation,[],[f21])).
% 4.01/1.00  
% 4.01/1.00  fof(f39,plain,(
% 4.01/1.00    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK3,sK4) = X0) )),
% 4.01/1.00    introduced(choice_axiom,[])).
% 4.01/1.00  
% 4.01/1.00  fof(f38,plain,(
% 4.01/1.00    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 4.01/1.00    introduced(choice_axiom,[])).
% 4.01/1.00  
% 4.01/1.00  fof(f40,plain,(
% 4.01/1.00    (k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & k4_tarski(sK3,sK4) = sK2),
% 4.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f39,f38])).
% 4.01/1.00  
% 4.01/1.00  fof(f82,plain,(
% 4.01/1.00    k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2),
% 4.01/1.00    inference(cnf_transformation,[],[f40])).
% 4.01/1.00  
% 4.01/1.00  fof(f81,plain,(
% 4.01/1.00    k4_tarski(sK3,sK4) = sK2),
% 4.01/1.00    inference(cnf_transformation,[],[f40])).
% 4.01/1.00  
% 4.01/1.00  fof(f19,axiom,(
% 4.01/1.00    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f79,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 4.01/1.00    inference(cnf_transformation,[],[f19])).
% 4.01/1.00  
% 4.01/1.00  fof(f80,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 4.01/1.00    inference(cnf_transformation,[],[f19])).
% 4.01/1.00  
% 4.01/1.00  fof(f14,axiom,(
% 4.01/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f29,plain,(
% 4.01/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 4.01/1.00    inference(nnf_transformation,[],[f14])).
% 4.01/1.00  
% 4.01/1.00  fof(f30,plain,(
% 4.01/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 4.01/1.00    inference(flattening,[],[f29])).
% 4.01/1.00  
% 4.01/1.00  fof(f57,plain,(
% 4.01/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f30])).
% 4.01/1.00  
% 4.01/1.00  fof(f56,plain,(
% 4.01/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 4.01/1.00    inference(cnf_transformation,[],[f30])).
% 4.01/1.00  
% 4.01/1.00  fof(f12,axiom,(
% 4.01/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f28,plain,(
% 4.01/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 4.01/1.00    inference(nnf_transformation,[],[f12])).
% 4.01/1.00  
% 4.01/1.00  fof(f53,plain,(
% 4.01/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f28])).
% 4.01/1.00  
% 4.01/1.00  fof(f5,axiom,(
% 4.01/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f45,plain,(
% 4.01/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f5])).
% 4.01/1.00  
% 4.01/1.00  fof(f6,axiom,(
% 4.01/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f46,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f6])).
% 4.01/1.00  
% 4.01/1.00  fof(f7,axiom,(
% 4.01/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f47,plain,(
% 4.01/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f7])).
% 4.01/1.00  
% 4.01/1.00  fof(f8,axiom,(
% 4.01/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f48,plain,(
% 4.01/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f8])).
% 4.01/1.00  
% 4.01/1.00  fof(f9,axiom,(
% 4.01/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f49,plain,(
% 4.01/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f9])).
% 4.01/1.00  
% 4.01/1.00  fof(f84,plain,(
% 4.01/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.01/1.00    inference(definition_unfolding,[],[f49,f83])).
% 4.01/1.00  
% 4.01/1.00  fof(f85,plain,(
% 4.01/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.01/1.00    inference(definition_unfolding,[],[f48,f84])).
% 4.01/1.00  
% 4.01/1.00  fof(f86,plain,(
% 4.01/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.01/1.00    inference(definition_unfolding,[],[f47,f85])).
% 4.01/1.00  
% 4.01/1.00  fof(f87,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.01/1.00    inference(definition_unfolding,[],[f46,f86])).
% 4.01/1.00  
% 4.01/1.00  fof(f91,plain,(
% 4.01/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.01/1.00    inference(definition_unfolding,[],[f45,f87])).
% 4.01/1.00  
% 4.01/1.00  fof(f95,plain,(
% 4.01/1.00    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.01/1.00    inference(definition_unfolding,[],[f53,f91])).
% 4.01/1.00  
% 4.01/1.00  fof(f15,axiom,(
% 4.01/1.00    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f23,plain,(
% 4.01/1.00    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 4.01/1.00    inference(ennf_transformation,[],[f15])).
% 4.01/1.00  
% 4.01/1.00  fof(f59,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 4.01/1.00    inference(cnf_transformation,[],[f23])).
% 4.01/1.00  
% 4.01/1.00  fof(f16,axiom,(
% 4.01/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f31,plain,(
% 4.01/1.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 4.01/1.00    inference(nnf_transformation,[],[f16])).
% 4.01/1.00  
% 4.01/1.00  fof(f60,plain,(
% 4.01/1.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 4.01/1.00    inference(cnf_transformation,[],[f31])).
% 4.01/1.00  
% 4.01/1.00  fof(f2,axiom,(
% 4.01/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f42,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.01/1.00    inference(cnf_transformation,[],[f2])).
% 4.01/1.00  
% 4.01/1.00  fof(f18,axiom,(
% 4.01/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f78,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.01/1.00    inference(cnf_transformation,[],[f18])).
% 4.01/1.00  
% 4.01/1.00  fof(f88,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.01/1.00    inference(definition_unfolding,[],[f78,f87])).
% 4.01/1.00  
% 4.01/1.00  fof(f89,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.01/1.00    inference(definition_unfolding,[],[f42,f88])).
% 4.01/1.00  
% 4.01/1.00  fof(f98,plain,(
% 4.01/1.00    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.01/1.00    inference(definition_unfolding,[],[f60,f89,f91,f91,f91])).
% 4.01/1.00  
% 4.01/1.00  fof(f101,plain,(
% 4.01/1.00    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 4.01/1.00    inference(equality_resolution,[],[f98])).
% 4.01/1.00  
% 4.01/1.00  fof(f1,axiom,(
% 4.01/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f22,plain,(
% 4.01/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.01/1.00    inference(rectify,[],[f1])).
% 4.01/1.00  
% 4.01/1.00  fof(f41,plain,(
% 4.01/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.01/1.00    inference(cnf_transformation,[],[f22])).
% 4.01/1.00  
% 4.01/1.00  fof(f92,plain,(
% 4.01/1.00    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 4.01/1.00    inference(definition_unfolding,[],[f41,f88])).
% 4.01/1.00  
% 4.01/1.00  fof(f4,axiom,(
% 4.01/1.00    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f44,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 4.01/1.00    inference(cnf_transformation,[],[f4])).
% 4.01/1.00  
% 4.01/1.00  fof(f13,axiom,(
% 4.01/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f54,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.01/1.00    inference(cnf_transformation,[],[f13])).
% 4.01/1.00  
% 4.01/1.00  fof(f90,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.01/1.00    inference(definition_unfolding,[],[f54,f87])).
% 4.01/1.00  
% 4.01/1.00  fof(f94,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0) )),
% 4.01/1.00    inference(definition_unfolding,[],[f44,f89,f90])).
% 4.01/1.00  
% 4.01/1.00  fof(f3,axiom,(
% 4.01/1.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 4.01/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/1.00  
% 4.01/1.00  fof(f43,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 4.01/1.00    inference(cnf_transformation,[],[f3])).
% 4.01/1.00  
% 4.01/1.00  fof(f93,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0) )),
% 4.01/1.00    inference(definition_unfolding,[],[f43,f88,f90])).
% 4.01/1.00  
% 4.01/1.00  fof(f58,plain,(
% 4.01/1.00    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 4.01/1.00    inference(cnf_transformation,[],[f23])).
% 4.01/1.00  
% 4.01/1.00  cnf(c_27,plain,
% 4.01/1.00      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
% 4.01/1.00      inference(cnf_transformation,[],[f108]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2192,plain,
% 4.01/1.00      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
% 4.01/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_24,plain,
% 4.01/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X5,X6) ),
% 4.01/1.00      inference(cnf_transformation,[],[f107]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2195,plain,
% 4.01/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6) != iProver_top
% 4.01/1.00      | r2_hidden(X5,X6) = iProver_top ),
% 4.01/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_4357,plain,
% 4.01/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_2192,c_2195]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_19,plain,
% 4.01/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X0,X6) ),
% 4.01/1.00      inference(cnf_transformation,[],[f102]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2200,plain,
% 4.01/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6) != iProver_top
% 4.01/1.00      | r2_hidden(X0,X6) = iProver_top ),
% 4.01/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_4352,plain,
% 4.01/1.00      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X0)) = iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_2192,c_2200]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_30,negated_conjecture,
% 4.01/1.00      ( k1_mcart_1(sK2) = sK2 | k2_mcart_1(sK2) = sK2 ),
% 4.01/1.00      inference(cnf_transformation,[],[f82]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_31,negated_conjecture,
% 4.01/1.00      ( k4_tarski(sK3,sK4) = sK2 ),
% 4.01/1.00      inference(cnf_transformation,[],[f81]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_29,plain,
% 4.01/1.00      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 4.01/1.00      inference(cnf_transformation,[],[f79]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2426,plain,
% 4.01/1.00      ( k1_mcart_1(sK2) = sK3 ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_31,c_29]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2437,plain,
% 4.01/1.00      ( k2_mcart_1(sK2) = sK2 | sK3 = sK2 ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_30,c_2426]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_28,plain,
% 4.01/1.00      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 4.01/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2423,plain,
% 4.01/1.00      ( k2_mcart_1(sK2) = sK4 ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_31,c_28]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2439,plain,
% 4.01/1.00      ( sK4 = sK2 | sK3 = sK2 ),
% 4.01/1.00      inference(demodulation,[status(thm)],[c_2437,c_2423]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2442,plain,
% 4.01/1.00      ( k4_tarski(sK3,sK2) = sK2 | sK3 = sK2 ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_2439,c_31]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_5,plain,
% 4.01/1.00      ( ~ r2_hidden(X0,X1)
% 4.01/1.00      | ~ r2_hidden(X2,X3)
% 4.01/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 4.01/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2212,plain,
% 4.01/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.01/1.00      | r2_hidden(X2,X3) != iProver_top
% 4.01/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 4.01/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_4017,plain,
% 4.01/1.00      ( sK3 = sK2
% 4.01/1.00      | r2_hidden(sK3,X0) != iProver_top
% 4.01/1.00      | r2_hidden(sK2,X1) != iProver_top
% 4.01/1.00      | r2_hidden(sK2,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_2442,c_2212]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_6,plain,
% 4.01/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 4.01/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2211,plain,
% 4.01/1.00      ( r2_hidden(X0,X1) = iProver_top
% 4.01/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 4.01/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_3491,plain,
% 4.01/1.00      ( r2_hidden(sK4,X0) = iProver_top
% 4.01/1.00      | r2_hidden(sK2,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_31,c_2211]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_4249,plain,
% 4.01/1.00      ( sK3 = sK2
% 4.01/1.00      | r2_hidden(sK4,X0) = iProver_top
% 4.01/1.00      | r2_hidden(sK3,X1) != iProver_top
% 4.01/1.00      | r2_hidden(sK2,X0) != iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_4017,c_3491]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_4530,plain,
% 4.01/1.00      ( sK3 = sK2
% 4.01/1.00      | r2_hidden(sK4,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,sK2)) = iProver_top
% 4.01/1.00      | r2_hidden(sK3,X5) != iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_4352,c_4249]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_4595,plain,
% 4.01/1.00      ( sK3 = sK2
% 4.01/1.00      | r2_hidden(sK4,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,sK2)) = iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_4352,c_4530]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_4016,plain,
% 4.01/1.00      ( r2_hidden(sK4,X0) != iProver_top
% 4.01/1.00      | r2_hidden(sK3,X1) != iProver_top
% 4.01/1.00      | r2_hidden(sK2,k2_zfmisc_1(X1,X0)) = iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_31,c_2212]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_3,plain,
% 4.01/1.00      ( ~ r2_hidden(X0,X1)
% 4.01/1.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 4.01/1.00      inference(cnf_transformation,[],[f95]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2214,plain,
% 4.01/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.01/1.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 4.01/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_8,plain,
% 4.01/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 4.01/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2209,plain,
% 4.01/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 4.01/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_4388,plain,
% 4.01/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 4.01/1.00      | r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_2214,c_2209]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_11,plain,
% 4.01/1.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 4.01/1.00      inference(cnf_transformation,[],[f101]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_0,plain,
% 4.01/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 4.01/1.00      inference(cnf_transformation,[],[f92]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2,plain,
% 4.01/1.00      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
% 4.01/1.00      inference(cnf_transformation,[],[f94]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_1,plain,
% 4.01/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
% 4.01/1.00      inference(cnf_transformation,[],[f93]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2289,plain,
% 4.01/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.01/1.00      inference(light_normalisation,[status(thm)],[c_2,c_1]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2360,plain,
% 4.01/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 4.01/1.00      inference(demodulation,[status(thm)],[c_11,c_0,c_2289]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_5745,plain,
% 4.01/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 4.01/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4388,c_2360]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_5754,plain,
% 4.01/1.00      ( r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 4.01/1.00      | r2_hidden(sK3,X0) != iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_4016,c_5745]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_5936,plain,
% 4.01/1.00      ( sK3 = sK2 | r2_hidden(sK3,X0) != iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_4595,c_5754]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_6809,plain,
% 4.01/1.00      ( sK3 = sK2 ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_4357,c_5936]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_6943,plain,
% 4.01/1.00      ( r2_hidden(sK4,X0) != iProver_top
% 4.01/1.00      | r2_hidden(sK2,X1) != iProver_top
% 4.01/1.00      | r2_hidden(sK2,k2_zfmisc_1(X1,X0)) = iProver_top ),
% 4.01/1.00      inference(demodulation,[status(thm)],[c_6809,c_4016]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_1318,plain,
% 4.01/1.00      ( r2_hidden(X0,X1)
% 4.01/1.00      | X2 != X3
% 4.01/1.00      | X4 != X0
% 4.01/1.00      | X5 != X6
% 4.01/1.00      | X7 != X8
% 4.01/1.00      | X9 != X10
% 4.01/1.00      | X11 != X12
% 4.01/1.00      | k6_enumset1(X4,X4,X4,X5,X7,X9,X11,X2) != X1 ),
% 4.01/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_1319,plain,
% 4.01/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
% 4.01/1.00      inference(unflattening,[status(thm)],[c_1318]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_1320,plain,
% 4.01/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 4.01/1.00      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_1322,plain,
% 4.01/1.00      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 4.01/1.00      inference(instantiation,[status(thm)],[c_1320]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_9,plain,
% 4.01/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 4.01/1.00      inference(cnf_transformation,[],[f58]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_2208,plain,
% 4.01/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 4.01/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_4389,plain,
% 4.01/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 4.01/1.00      | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_2214,c_2208]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_5950,plain,
% 4.01/1.00      ( r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != iProver_top ),
% 4.01/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4389,c_2360]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_5958,plain,
% 4.01/1.00      ( r2_hidden(sK4,X0) != iProver_top
% 4.01/1.00      | r2_hidden(sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_4016,c_5950]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_6941,plain,
% 4.01/1.00      ( r2_hidden(sK4,X0) != iProver_top
% 4.01/1.00      | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 4.01/1.00      inference(demodulation,[status(thm)],[c_6809,c_5958]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_7709,plain,
% 4.01/1.00      ( r2_hidden(sK4,X0) != iProver_top ),
% 4.01/1.00      inference(global_propositional_subsumption,
% 4.01/1.00                [status(thm)],
% 4.01/1.00                [c_6943,c_1322,c_6941]) ).
% 4.01/1.00  
% 4.01/1.00  cnf(c_7716,plain,
% 4.01/1.00      ( $false ),
% 4.01/1.00      inference(superposition,[status(thm)],[c_4357,c_7709]) ).
% 4.01/1.00  
% 4.01/1.00  
% 4.01/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/1.00  
% 4.01/1.00  ------                               Statistics
% 4.01/1.00  
% 4.01/1.00  ------ General
% 4.01/1.00  
% 4.01/1.00  abstr_ref_over_cycles:                  0
% 4.01/1.00  abstr_ref_under_cycles:                 0
% 4.01/1.00  gc_basic_clause_elim:                   0
% 4.01/1.00  forced_gc_time:                         0
% 4.01/1.00  parsing_time:                           0.008
% 4.01/1.00  unif_index_cands_time:                  0.
% 4.01/1.00  unif_index_add_time:                    0.
% 4.01/1.00  orderings_time:                         0.
% 4.01/1.00  out_proof_time:                         0.01
% 4.01/1.00  total_time:                             0.455
% 4.01/1.00  num_of_symbols:                         47
% 4.01/1.00  num_of_terms:                           14545
% 4.01/1.00  
% 4.01/1.00  ------ Preprocessing
% 4.01/1.00  
% 4.01/1.00  num_of_splits:                          0
% 4.01/1.00  num_of_split_atoms:                     0
% 4.01/1.00  num_of_reused_defs:                     0
% 4.01/1.00  num_eq_ax_congr_red:                    30
% 4.01/1.00  num_of_sem_filtered_clauses:            1
% 4.01/1.00  num_of_subtypes:                        0
% 4.01/1.00  monotx_restored_types:                  0
% 4.01/1.00  sat_num_of_epr_types:                   0
% 4.01/1.00  sat_num_of_non_cyclic_types:            0
% 4.01/1.00  sat_guarded_non_collapsed_types:        0
% 4.01/1.00  num_pure_diseq_elim:                    0
% 4.01/1.00  simp_replaced_by:                       0
% 4.01/1.00  res_preprocessed:                       121
% 4.01/1.00  prep_upred:                             0
% 4.01/1.00  prep_unflattend:                        60
% 4.01/1.00  smt_new_axioms:                         0
% 4.01/1.00  pred_elim_cands:                        3
% 4.01/1.00  pred_elim:                              0
% 4.01/1.00  pred_elim_cl:                           0
% 4.01/1.00  pred_elim_cycles:                       2
% 4.01/1.00  merged_defs:                            6
% 4.01/1.00  merged_defs_ncl:                        0
% 4.01/1.00  bin_hyper_res:                          6
% 4.01/1.00  prep_cycles:                            3
% 4.01/1.00  pred_elim_time:                         0.02
% 4.01/1.00  splitting_time:                         0.
% 4.01/1.00  sem_filter_time:                        0.
% 4.01/1.00  monotx_time:                            0.
% 4.01/1.00  subtype_inf_time:                       0.
% 4.01/1.00  
% 4.01/1.00  ------ Problem properties
% 4.01/1.00  
% 4.01/1.00  clauses:                                32
% 4.01/1.00  conjectures:                            2
% 4.01/1.00  epr:                                    7
% 4.01/1.00  horn:                                   28
% 4.01/1.00  ground:                                 2
% 4.01/1.00  unary:                                  8
% 4.01/1.00  binary:                                 15
% 4.01/1.00  lits:                                   75
% 4.01/1.00  lits_eq:                                32
% 4.01/1.00  fd_pure:                                0
% 4.01/1.00  fd_pseudo:                              0
% 4.01/1.00  fd_cond:                                2
% 4.01/1.00  fd_pseudo_cond:                         3
% 4.01/1.00  ac_symbols:                             0
% 4.01/1.00  
% 4.01/1.00  ------ Propositional Solver
% 4.01/1.00  
% 4.01/1.00  prop_solver_calls:                      23
% 4.01/1.00  prop_fast_solver_calls:                 1071
% 4.01/1.00  smt_solver_calls:                       0
% 4.01/1.00  smt_fast_solver_calls:                  0
% 4.01/1.00  prop_num_of_clauses:                    2833
% 4.01/1.00  prop_preprocess_simplified:             10632
% 4.01/1.00  prop_fo_subsumed:                       4
% 4.01/1.00  prop_solver_time:                       0.
% 4.01/1.00  smt_solver_time:                        0.
% 4.01/1.00  smt_fast_solver_time:                   0.
% 4.01/1.00  prop_fast_solver_time:                  0.
% 4.01/1.00  prop_unsat_core_time:                   0.
% 4.01/1.00  
% 4.01/1.00  ------ QBF
% 4.01/1.00  
% 4.01/1.00  qbf_q_res:                              0
% 4.01/1.00  qbf_num_tautologies:                    0
% 4.01/1.00  qbf_prep_cycles:                        0
% 4.01/1.00  
% 4.01/1.00  ------ BMC1
% 4.01/1.00  
% 4.01/1.00  bmc1_current_bound:                     -1
% 4.01/1.00  bmc1_last_solved_bound:                 -1
% 4.01/1.00  bmc1_unsat_core_size:                   -1
% 4.01/1.00  bmc1_unsat_core_parents_size:           -1
% 4.01/1.00  bmc1_merge_next_fun:                    0
% 4.01/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.01/1.00  
% 4.01/1.00  ------ Instantiation
% 4.01/1.00  
% 4.01/1.00  inst_num_of_clauses:                    982
% 4.01/1.00  inst_num_in_passive:                    432
% 4.01/1.00  inst_num_in_active:                     340
% 4.01/1.00  inst_num_in_unprocessed:                210
% 4.01/1.00  inst_num_of_loops:                      420
% 4.01/1.00  inst_num_of_learning_restarts:          0
% 4.01/1.00  inst_num_moves_active_passive:          79
% 4.01/1.00  inst_lit_activity:                      0
% 4.01/1.00  inst_lit_activity_moves:                0
% 4.01/1.00  inst_num_tautologies:                   0
% 4.01/1.00  inst_num_prop_implied:                  0
% 4.01/1.00  inst_num_existing_simplified:           0
% 4.01/1.00  inst_num_eq_res_simplified:             0
% 4.01/1.00  inst_num_child_elim:                    0
% 4.01/1.00  inst_num_of_dismatching_blockings:      245
% 4.01/1.00  inst_num_of_non_proper_insts:           667
% 4.01/1.00  inst_num_of_duplicates:                 0
% 4.01/1.00  inst_inst_num_from_inst_to_res:         0
% 4.01/1.00  inst_dismatching_checking_time:         0.
% 4.01/1.00  
% 4.01/1.00  ------ Resolution
% 4.01/1.00  
% 4.01/1.00  res_num_of_clauses:                     0
% 4.01/1.00  res_num_in_passive:                     0
% 4.01/1.00  res_num_in_active:                      0
% 4.01/1.00  res_num_of_loops:                       124
% 4.01/1.00  res_forward_subset_subsumed:            20
% 4.01/1.00  res_backward_subset_subsumed:           0
% 4.01/1.00  res_forward_subsumed:                   0
% 4.01/1.00  res_backward_subsumed:                  0
% 4.01/1.00  res_forward_subsumption_resolution:     0
% 4.01/1.00  res_backward_subsumption_resolution:    0
% 4.01/1.00  res_clause_to_clause_subsumption:       2104
% 4.01/1.00  res_orphan_elimination:                 0
% 4.01/1.00  res_tautology_del:                      45
% 4.01/1.00  res_num_eq_res_simplified:              0
% 4.01/1.00  res_num_sel_changes:                    0
% 4.01/1.00  res_moves_from_active_to_pass:          0
% 4.01/1.00  
% 4.01/1.00  ------ Superposition
% 4.01/1.00  
% 4.01/1.00  sup_time_total:                         0.
% 4.01/1.00  sup_time_generating:                    0.
% 4.01/1.00  sup_time_sim_full:                      0.
% 4.01/1.00  sup_time_sim_immed:                     0.
% 4.01/1.00  
% 4.01/1.00  sup_num_of_clauses:                     51
% 4.01/1.00  sup_num_in_active:                      47
% 4.01/1.00  sup_num_in_passive:                     4
% 4.01/1.00  sup_num_of_loops:                       83
% 4.01/1.00  sup_fw_superposition:                   88
% 4.01/1.00  sup_bw_superposition:                   72
% 4.01/1.00  sup_immediate_simplified:               29
% 4.01/1.00  sup_given_eliminated:                   0
% 4.01/1.00  comparisons_done:                       0
% 4.01/1.00  comparisons_avoided:                    2
% 4.01/1.00  
% 4.01/1.00  ------ Simplifications
% 4.01/1.00  
% 4.01/1.00  
% 4.01/1.00  sim_fw_subset_subsumed:                 4
% 4.01/1.00  sim_bw_subset_subsumed:                 45
% 4.01/1.00  sim_fw_subsumed:                        17
% 4.01/1.00  sim_bw_subsumed:                        0
% 4.01/1.00  sim_fw_subsumption_res:                 0
% 4.01/1.00  sim_bw_subsumption_res:                 0
% 4.01/1.01  sim_tautology_del:                      7
% 4.01/1.01  sim_eq_tautology_del:                   3
% 4.01/1.01  sim_eq_res_simp:                        0
% 4.01/1.01  sim_fw_demodulated:                     3
% 4.01/1.01  sim_bw_demodulated:                     7
% 4.01/1.01  sim_light_normalised:                   1
% 4.01/1.01  sim_joinable_taut:                      0
% 4.01/1.01  sim_joinable_simp:                      0
% 4.01/1.01  sim_ac_normalised:                      0
% 4.01/1.01  sim_smt_subsumption:                    0
% 4.01/1.01  
%------------------------------------------------------------------------------
