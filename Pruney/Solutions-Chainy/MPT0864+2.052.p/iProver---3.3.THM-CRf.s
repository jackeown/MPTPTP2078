%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:55 EST 2020

% Result     : Theorem 7.25s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 369 expanded)
%              Number of clauses        :   49 (  83 expanded)
%              Number of leaves         :   21 (  97 expanded)
%              Depth                    :   19
%              Number of atoms          :  377 (1504 expanded)
%              Number of equality atoms :  280 (1150 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f23,plain,(
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

fof(f28,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( sP2(X5,X4,X3,X2,X1,X0,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP2(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f23,f28])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP2(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP2(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP2(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f116,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP2(X5,X4,X3,X2,X1,X0,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f99,f105])).

fof(f133,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP2(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f116])).

fof(f41,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP2(X5,X4,X3,X2,X1,X0,X6)
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
        | ~ sP2(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP2(X5,X4,X3,X2,X1,X0,X6)
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
        | ~ sP2(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6)
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
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6) != X0
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK4(X0,X1,X2,X3,X4,X5,X6) != X5 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK4(X0,X1,X2,X3,X4,X5,X6) = X0
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK4(X0,X1,X2,X3,X4,X5,X6) = X5
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6) != X0
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK4(X0,X1,X2,X3,X4,X5,X6) != X5 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK4(X0,X1,X2,X3,X4,X5,X6) = X0
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK4(X0,X1,X2,X3,X4,X5,X6) = X5
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
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
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | ~ sP2(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f132,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP2(X0,X1,X2,X3,X4,X8,X6) ) ),
    inference(equality_resolution,[],[f86])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X0 != X8
      | ~ sP2(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f127,plain,(
    ! [X6,X4,X2,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP2(X8,X1,X2,X3,X4,X5,X6) ) ),
    inference(equality_resolution,[],[f91])).

fof(f19,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f24,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK6,sK7) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK5) = sK5
        | k1_mcart_1(sK5) = sK5 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK5 ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( k2_mcart_1(sK5) = sK5
      | k1_mcart_1(sK5) = sK5 )
    & k4_tarski(sK6,sK7) = sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f24,f48,f47])).

fof(f104,plain,
    ( k2_mcart_1(sK5) = sK5
    | k1_mcart_1(sK5) = sK5 ),
    inference(cnf_transformation,[],[f49])).

fof(f103,plain,(
    k4_tarski(sK6,sK7) = sK5 ),
    inference(cnf_transformation,[],[f49])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f39])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f106,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f73,f105])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f106])).

fof(f108,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f71,f107])).

fof(f109,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f108])).

fof(f110,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f69,f109])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f110])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f114,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f84,f52,f110])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_42,plain,
    ( sP2(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_3237,plain,
    ( sP2(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_39,plain,
    ( ~ sP2(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X5,X6) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_3240,plain,
    ( sP2(X0,X1,X2,X3,X4,X5,X6) != iProver_top
    | r2_hidden(X5,X6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5241,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3237,c_3240])).

cnf(c_34,plain,
    ( ~ sP2(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X0,X6) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_3245,plain,
    ( sP2(X0,X1,X2,X3,X4,X5,X6) != iProver_top
    | r2_hidden(X0,X6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5236,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3237,c_3245])).

cnf(c_45,negated_conjecture,
    ( k1_mcart_1(sK5) = sK5
    | k2_mcart_1(sK5) = sK5 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_46,negated_conjecture,
    ( k4_tarski(sK6,sK7) = sK5 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_44,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3591,plain,
    ( k1_mcart_1(sK5) = sK6 ),
    inference(superposition,[status(thm)],[c_46,c_44])).

cnf(c_3593,plain,
    ( k2_mcart_1(sK5) = sK5
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_45,c_3591])).

cnf(c_43,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3585,plain,
    ( k2_mcart_1(sK5) = sK7 ),
    inference(superposition,[status(thm)],[c_46,c_43])).

cnf(c_3595,plain,
    ( sK7 = sK5
    | sK6 = sK5 ),
    inference(demodulation,[status(thm)],[c_3593,c_3585])).

cnf(c_3736,plain,
    ( k4_tarski(sK6,sK5) = sK5
    | sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_3595,c_46])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3257,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5098,plain,
    ( sK6 = sK5
    | r2_hidden(sK6,X0) != iProver_top
    | r2_hidden(sK5,X1) != iProver_top
    | r2_hidden(sK5,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3736,c_3257])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3256,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3926,plain,
    ( r2_hidden(sK7,X0) = iProver_top
    | r2_hidden(sK5,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_46,c_3256])).

cnf(c_5656,plain,
    ( sK6 = sK5
    | r2_hidden(sK7,X0) = iProver_top
    | r2_hidden(sK6,X1) != iProver_top
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5098,c_3926])).

cnf(c_6533,plain,
    ( sK6 = sK5
    | r2_hidden(sK7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,sK5)) = iProver_top
    | r2_hidden(sK6,X5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5236,c_5656])).

cnf(c_7599,plain,
    ( sK6 = sK5
    | r2_hidden(sK7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5236,c_6533])).

cnf(c_5097,plain,
    ( r2_hidden(sK7,X0) != iProver_top
    | r2_hidden(sK6,X1) != iProver_top
    | r2_hidden(sK5,k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_46,c_3257])).

cnf(c_18,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3259,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3254,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5410,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3259,c_3254])).

cnf(c_0,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_26,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3610,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_26])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3611,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3610,c_1])).

cnf(c_20482,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5410,c_3611])).

cnf(c_20491,plain,
    ( r2_hidden(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5097,c_20482])).

cnf(c_20983,plain,
    ( sK6 = sK5
    | r2_hidden(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7599,c_20491])).

cnf(c_21000,plain,
    ( sK6 = sK5 ),
    inference(superposition,[status(thm)],[c_5241,c_20983])).

cnf(c_21483,plain,
    ( r2_hidden(sK7,X0) != iProver_top
    | r2_hidden(sK5,X1) != iProver_top
    | r2_hidden(sK5,k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_21000,c_5097])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3253,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5411,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
    | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3259,c_3253])).

cnf(c_22085,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5411,c_3611])).

cnf(c_22093,plain,
    ( r2_hidden(sK7,X0) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21483,c_22085])).

cnf(c_22232,plain,
    ( r2_hidden(sK7,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_22093,c_5236])).

cnf(c_22236,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5241,c_22232])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n007.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 15:23:21 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running in FOF mode
% 7.25/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.25/1.47  
% 7.25/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.25/1.47  
% 7.25/1.47  ------  iProver source info
% 7.25/1.47  
% 7.25/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.25/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.25/1.47  git: non_committed_changes: false
% 7.25/1.47  git: last_make_outside_of_git: false
% 7.25/1.47  
% 7.25/1.47  ------ 
% 7.25/1.47  
% 7.25/1.47  ------ Input Options
% 7.25/1.47  
% 7.25/1.47  --out_options                           all
% 7.25/1.47  --tptp_safe_out                         true
% 7.25/1.47  --problem_path                          ""
% 7.25/1.47  --include_path                          ""
% 7.25/1.47  --clausifier                            res/vclausify_rel
% 7.25/1.47  --clausifier_options                    --mode clausify
% 7.25/1.47  --stdin                                 false
% 7.25/1.47  --stats_out                             all
% 7.25/1.47  
% 7.25/1.47  ------ General Options
% 7.25/1.47  
% 7.25/1.47  --fof                                   false
% 7.25/1.47  --time_out_real                         305.
% 7.25/1.47  --time_out_virtual                      -1.
% 7.25/1.47  --symbol_type_check                     false
% 7.25/1.47  --clausify_out                          false
% 7.25/1.47  --sig_cnt_out                           false
% 7.25/1.47  --trig_cnt_out                          false
% 7.25/1.47  --trig_cnt_out_tolerance                1.
% 7.25/1.47  --trig_cnt_out_sk_spl                   false
% 7.25/1.47  --abstr_cl_out                          false
% 7.25/1.47  
% 7.25/1.47  ------ Global Options
% 7.25/1.47  
% 7.25/1.47  --schedule                              default
% 7.25/1.47  --add_important_lit                     false
% 7.25/1.47  --prop_solver_per_cl                    1000
% 7.25/1.47  --min_unsat_core                        false
% 7.25/1.47  --soft_assumptions                      false
% 7.25/1.47  --soft_lemma_size                       3
% 7.25/1.47  --prop_impl_unit_size                   0
% 7.25/1.47  --prop_impl_unit                        []
% 7.25/1.47  --share_sel_clauses                     true
% 7.25/1.47  --reset_solvers                         false
% 7.25/1.47  --bc_imp_inh                            [conj_cone]
% 7.25/1.47  --conj_cone_tolerance                   3.
% 7.25/1.47  --extra_neg_conj                        none
% 7.25/1.47  --large_theory_mode                     true
% 7.25/1.47  --prolific_symb_bound                   200
% 7.25/1.47  --lt_threshold                          2000
% 7.25/1.47  --clause_weak_htbl                      true
% 7.25/1.47  --gc_record_bc_elim                     false
% 7.25/1.47  
% 7.25/1.47  ------ Preprocessing Options
% 7.25/1.47  
% 7.25/1.47  --preprocessing_flag                    true
% 7.25/1.47  --time_out_prep_mult                    0.1
% 7.25/1.47  --splitting_mode                        input
% 7.25/1.47  --splitting_grd                         true
% 7.25/1.47  --splitting_cvd                         false
% 7.25/1.47  --splitting_cvd_svl                     false
% 7.25/1.47  --splitting_nvd                         32
% 7.25/1.47  --sub_typing                            true
% 7.25/1.47  --prep_gs_sim                           true
% 7.25/1.47  --prep_unflatten                        true
% 7.25/1.47  --prep_res_sim                          true
% 7.25/1.47  --prep_upred                            true
% 7.25/1.47  --prep_sem_filter                       exhaustive
% 7.25/1.47  --prep_sem_filter_out                   false
% 7.25/1.47  --pred_elim                             true
% 7.25/1.47  --res_sim_input                         true
% 7.25/1.47  --eq_ax_congr_red                       true
% 7.25/1.47  --pure_diseq_elim                       true
% 7.25/1.47  --brand_transform                       false
% 7.25/1.47  --non_eq_to_eq                          false
% 7.25/1.47  --prep_def_merge                        true
% 7.25/1.47  --prep_def_merge_prop_impl              false
% 7.25/1.47  --prep_def_merge_mbd                    true
% 7.25/1.47  --prep_def_merge_tr_red                 false
% 7.25/1.47  --prep_def_merge_tr_cl                  false
% 7.25/1.47  --smt_preprocessing                     true
% 7.25/1.47  --smt_ac_axioms                         fast
% 7.25/1.47  --preprocessed_out                      false
% 7.25/1.47  --preprocessed_stats                    false
% 7.25/1.47  
% 7.25/1.47  ------ Abstraction refinement Options
% 7.25/1.47  
% 7.25/1.47  --abstr_ref                             []
% 7.25/1.47  --abstr_ref_prep                        false
% 7.25/1.47  --abstr_ref_until_sat                   false
% 7.25/1.47  --abstr_ref_sig_restrict                funpre
% 7.25/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.47  --abstr_ref_under                       []
% 7.25/1.47  
% 7.25/1.47  ------ SAT Options
% 7.25/1.47  
% 7.25/1.47  --sat_mode                              false
% 7.25/1.47  --sat_fm_restart_options                ""
% 7.25/1.47  --sat_gr_def                            false
% 7.25/1.47  --sat_epr_types                         true
% 7.25/1.47  --sat_non_cyclic_types                  false
% 7.25/1.47  --sat_finite_models                     false
% 7.25/1.47  --sat_fm_lemmas                         false
% 7.25/1.47  --sat_fm_prep                           false
% 7.25/1.47  --sat_fm_uc_incr                        true
% 7.25/1.47  --sat_out_model                         small
% 7.25/1.47  --sat_out_clauses                       false
% 7.25/1.47  
% 7.25/1.47  ------ QBF Options
% 7.25/1.47  
% 7.25/1.47  --qbf_mode                              false
% 7.25/1.47  --qbf_elim_univ                         false
% 7.25/1.47  --qbf_dom_inst                          none
% 7.25/1.47  --qbf_dom_pre_inst                      false
% 7.25/1.47  --qbf_sk_in                             false
% 7.25/1.47  --qbf_pred_elim                         true
% 7.25/1.47  --qbf_split                             512
% 7.25/1.47  
% 7.25/1.47  ------ BMC1 Options
% 7.25/1.47  
% 7.25/1.47  --bmc1_incremental                      false
% 7.25/1.47  --bmc1_axioms                           reachable_all
% 7.25/1.47  --bmc1_min_bound                        0
% 7.25/1.47  --bmc1_max_bound                        -1
% 7.25/1.47  --bmc1_max_bound_default                -1
% 7.25/1.47  --bmc1_symbol_reachability              true
% 7.25/1.47  --bmc1_property_lemmas                  false
% 7.25/1.47  --bmc1_k_induction                      false
% 7.25/1.47  --bmc1_non_equiv_states                 false
% 7.25/1.47  --bmc1_deadlock                         false
% 7.25/1.47  --bmc1_ucm                              false
% 7.25/1.47  --bmc1_add_unsat_core                   none
% 7.25/1.47  --bmc1_unsat_core_children              false
% 7.25/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.47  --bmc1_out_stat                         full
% 7.25/1.47  --bmc1_ground_init                      false
% 7.25/1.47  --bmc1_pre_inst_next_state              false
% 7.25/1.47  --bmc1_pre_inst_state                   false
% 7.25/1.47  --bmc1_pre_inst_reach_state             false
% 7.25/1.47  --bmc1_out_unsat_core                   false
% 7.25/1.47  --bmc1_aig_witness_out                  false
% 7.25/1.47  --bmc1_verbose                          false
% 7.25/1.47  --bmc1_dump_clauses_tptp                false
% 7.25/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.47  --bmc1_dump_file                        -
% 7.25/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.47  --bmc1_ucm_extend_mode                  1
% 7.25/1.47  --bmc1_ucm_init_mode                    2
% 7.25/1.47  --bmc1_ucm_cone_mode                    none
% 7.25/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.47  --bmc1_ucm_relax_model                  4
% 7.25/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.47  --bmc1_ucm_layered_model                none
% 7.25/1.47  --bmc1_ucm_max_lemma_size               10
% 7.25/1.47  
% 7.25/1.47  ------ AIG Options
% 7.25/1.47  
% 7.25/1.47  --aig_mode                              false
% 7.25/1.47  
% 7.25/1.47  ------ Instantiation Options
% 7.25/1.47  
% 7.25/1.47  --instantiation_flag                    true
% 7.25/1.47  --inst_sos_flag                         false
% 7.25/1.47  --inst_sos_phase                        true
% 7.25/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.47  --inst_lit_sel_side                     num_symb
% 7.25/1.47  --inst_solver_per_active                1400
% 7.25/1.47  --inst_solver_calls_frac                1.
% 7.25/1.47  --inst_passive_queue_type               priority_queues
% 7.25/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.47  --inst_passive_queues_freq              [25;2]
% 7.25/1.47  --inst_dismatching                      true
% 7.25/1.47  --inst_eager_unprocessed_to_passive     true
% 7.25/1.47  --inst_prop_sim_given                   true
% 7.25/1.47  --inst_prop_sim_new                     false
% 7.25/1.47  --inst_subs_new                         false
% 7.25/1.47  --inst_eq_res_simp                      false
% 7.25/1.47  --inst_subs_given                       false
% 7.25/1.47  --inst_orphan_elimination               true
% 7.25/1.47  --inst_learning_loop_flag               true
% 7.25/1.47  --inst_learning_start                   3000
% 7.25/1.47  --inst_learning_factor                  2
% 7.25/1.47  --inst_start_prop_sim_after_learn       3
% 7.25/1.47  --inst_sel_renew                        solver
% 7.25/1.47  --inst_lit_activity_flag                true
% 7.25/1.47  --inst_restr_to_given                   false
% 7.25/1.47  --inst_activity_threshold               500
% 7.25/1.47  --inst_out_proof                        true
% 7.25/1.47  
% 7.25/1.47  ------ Resolution Options
% 7.25/1.47  
% 7.25/1.47  --resolution_flag                       true
% 7.25/1.47  --res_lit_sel                           adaptive
% 7.25/1.47  --res_lit_sel_side                      none
% 7.25/1.47  --res_ordering                          kbo
% 7.25/1.47  --res_to_prop_solver                    active
% 7.25/1.47  --res_prop_simpl_new                    false
% 7.25/1.47  --res_prop_simpl_given                  true
% 7.25/1.47  --res_passive_queue_type                priority_queues
% 7.25/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.47  --res_passive_queues_freq               [15;5]
% 7.25/1.47  --res_forward_subs                      full
% 7.25/1.47  --res_backward_subs                     full
% 7.25/1.47  --res_forward_subs_resolution           true
% 7.25/1.47  --res_backward_subs_resolution          true
% 7.25/1.47  --res_orphan_elimination                true
% 7.25/1.47  --res_time_limit                        2.
% 7.25/1.47  --res_out_proof                         true
% 7.25/1.47  
% 7.25/1.47  ------ Superposition Options
% 7.25/1.47  
% 7.25/1.47  --superposition_flag                    true
% 7.25/1.47  --sup_passive_queue_type                priority_queues
% 7.25/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.47  --demod_completeness_check              fast
% 7.25/1.47  --demod_use_ground                      true
% 7.25/1.47  --sup_to_prop_solver                    passive
% 7.25/1.47  --sup_prop_simpl_new                    true
% 7.25/1.47  --sup_prop_simpl_given                  true
% 7.25/1.47  --sup_fun_splitting                     false
% 7.25/1.47  --sup_smt_interval                      50000
% 7.25/1.47  
% 7.25/1.47  ------ Superposition Simplification Setup
% 7.25/1.47  
% 7.25/1.47  --sup_indices_passive                   []
% 7.25/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.47  --sup_full_bw                           [BwDemod]
% 7.25/1.47  --sup_immed_triv                        [TrivRules]
% 7.25/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.47  --sup_immed_bw_main                     []
% 7.25/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.47  
% 7.25/1.47  ------ Combination Options
% 7.25/1.47  
% 7.25/1.47  --comb_res_mult                         3
% 7.25/1.47  --comb_sup_mult                         2
% 7.25/1.47  --comb_inst_mult                        10
% 7.25/1.47  
% 7.25/1.47  ------ Debug Options
% 7.25/1.47  
% 7.25/1.47  --dbg_backtrace                         false
% 7.25/1.47  --dbg_dump_prop_clauses                 false
% 7.25/1.47  --dbg_dump_prop_clauses_file            -
% 7.25/1.47  --dbg_out_stat                          false
% 7.25/1.47  ------ Parsing...
% 7.25/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.25/1.47  
% 7.25/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.25/1.47  
% 7.25/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.25/1.47  
% 7.25/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.25/1.47  ------ Proving...
% 7.25/1.47  ------ Problem Properties 
% 7.25/1.47  
% 7.25/1.47  
% 7.25/1.47  clauses                                 47
% 7.25/1.47  conjectures                             2
% 7.25/1.47  EPR                                     19
% 7.25/1.47  Horn                                    42
% 7.25/1.47  unary                                   18
% 7.25/1.47  binary                                  15
% 7.25/1.47  lits                                    107
% 7.25/1.47  lits eq                                 40
% 7.25/1.47  fd_pure                                 0
% 7.25/1.47  fd_pseudo                               0
% 7.25/1.47  fd_cond                                 2
% 7.25/1.47  fd_pseudo_cond                          4
% 7.25/1.47  AC symbols                              0
% 7.25/1.47  
% 7.25/1.47  ------ Schedule dynamic 5 is on 
% 7.25/1.47  
% 7.25/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.25/1.47  
% 7.25/1.47  
% 7.25/1.47  ------ 
% 7.25/1.47  Current options:
% 7.25/1.47  ------ 
% 7.25/1.47  
% 7.25/1.47  ------ Input Options
% 7.25/1.47  
% 7.25/1.47  --out_options                           all
% 7.25/1.47  --tptp_safe_out                         true
% 7.25/1.47  --problem_path                          ""
% 7.25/1.47  --include_path                          ""
% 7.25/1.47  --clausifier                            res/vclausify_rel
% 7.25/1.47  --clausifier_options                    --mode clausify
% 7.25/1.47  --stdin                                 false
% 7.25/1.47  --stats_out                             all
% 7.25/1.47  
% 7.25/1.47  ------ General Options
% 7.25/1.47  
% 7.25/1.47  --fof                                   false
% 7.25/1.47  --time_out_real                         305.
% 7.25/1.47  --time_out_virtual                      -1.
% 7.25/1.47  --symbol_type_check                     false
% 7.25/1.47  --clausify_out                          false
% 7.25/1.47  --sig_cnt_out                           false
% 7.25/1.47  --trig_cnt_out                          false
% 7.25/1.47  --trig_cnt_out_tolerance                1.
% 7.25/1.47  --trig_cnt_out_sk_spl                   false
% 7.25/1.47  --abstr_cl_out                          false
% 7.25/1.47  
% 7.25/1.47  ------ Global Options
% 7.25/1.47  
% 7.25/1.47  --schedule                              default
% 7.25/1.47  --add_important_lit                     false
% 7.25/1.47  --prop_solver_per_cl                    1000
% 7.25/1.47  --min_unsat_core                        false
% 7.25/1.47  --soft_assumptions                      false
% 7.25/1.47  --soft_lemma_size                       3
% 7.25/1.47  --prop_impl_unit_size                   0
% 7.25/1.47  --prop_impl_unit                        []
% 7.25/1.47  --share_sel_clauses                     true
% 7.25/1.47  --reset_solvers                         false
% 7.25/1.47  --bc_imp_inh                            [conj_cone]
% 7.25/1.47  --conj_cone_tolerance                   3.
% 7.25/1.47  --extra_neg_conj                        none
% 7.25/1.47  --large_theory_mode                     true
% 7.25/1.47  --prolific_symb_bound                   200
% 7.25/1.47  --lt_threshold                          2000
% 7.25/1.47  --clause_weak_htbl                      true
% 7.25/1.47  --gc_record_bc_elim                     false
% 7.25/1.47  
% 7.25/1.47  ------ Preprocessing Options
% 7.25/1.47  
% 7.25/1.47  --preprocessing_flag                    true
% 7.25/1.47  --time_out_prep_mult                    0.1
% 7.25/1.47  --splitting_mode                        input
% 7.25/1.47  --splitting_grd                         true
% 7.25/1.47  --splitting_cvd                         false
% 7.25/1.47  --splitting_cvd_svl                     false
% 7.25/1.47  --splitting_nvd                         32
% 7.25/1.47  --sub_typing                            true
% 7.25/1.47  --prep_gs_sim                           true
% 7.25/1.47  --prep_unflatten                        true
% 7.25/1.47  --prep_res_sim                          true
% 7.25/1.47  --prep_upred                            true
% 7.25/1.47  --prep_sem_filter                       exhaustive
% 7.25/1.47  --prep_sem_filter_out                   false
% 7.25/1.47  --pred_elim                             true
% 7.25/1.47  --res_sim_input                         true
% 7.25/1.47  --eq_ax_congr_red                       true
% 7.25/1.47  --pure_diseq_elim                       true
% 7.25/1.47  --brand_transform                       false
% 7.25/1.47  --non_eq_to_eq                          false
% 7.25/1.47  --prep_def_merge                        true
% 7.25/1.47  --prep_def_merge_prop_impl              false
% 7.25/1.47  --prep_def_merge_mbd                    true
% 7.25/1.47  --prep_def_merge_tr_red                 false
% 7.25/1.47  --prep_def_merge_tr_cl                  false
% 7.25/1.47  --smt_preprocessing                     true
% 7.25/1.47  --smt_ac_axioms                         fast
% 7.25/1.47  --preprocessed_out                      false
% 7.25/1.47  --preprocessed_stats                    false
% 7.25/1.47  
% 7.25/1.47  ------ Abstraction refinement Options
% 7.25/1.47  
% 7.25/1.47  --abstr_ref                             []
% 7.25/1.47  --abstr_ref_prep                        false
% 7.25/1.47  --abstr_ref_until_sat                   false
% 7.25/1.47  --abstr_ref_sig_restrict                funpre
% 7.25/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.25/1.47  --abstr_ref_under                       []
% 7.25/1.47  
% 7.25/1.47  ------ SAT Options
% 7.25/1.47  
% 7.25/1.47  --sat_mode                              false
% 7.25/1.47  --sat_fm_restart_options                ""
% 7.25/1.47  --sat_gr_def                            false
% 7.25/1.47  --sat_epr_types                         true
% 7.25/1.47  --sat_non_cyclic_types                  false
% 7.25/1.47  --sat_finite_models                     false
% 7.25/1.47  --sat_fm_lemmas                         false
% 7.25/1.47  --sat_fm_prep                           false
% 7.25/1.47  --sat_fm_uc_incr                        true
% 7.25/1.47  --sat_out_model                         small
% 7.25/1.47  --sat_out_clauses                       false
% 7.25/1.47  
% 7.25/1.47  ------ QBF Options
% 7.25/1.47  
% 7.25/1.47  --qbf_mode                              false
% 7.25/1.47  --qbf_elim_univ                         false
% 7.25/1.47  --qbf_dom_inst                          none
% 7.25/1.47  --qbf_dom_pre_inst                      false
% 7.25/1.47  --qbf_sk_in                             false
% 7.25/1.47  --qbf_pred_elim                         true
% 7.25/1.47  --qbf_split                             512
% 7.25/1.47  
% 7.25/1.47  ------ BMC1 Options
% 7.25/1.47  
% 7.25/1.47  --bmc1_incremental                      false
% 7.25/1.47  --bmc1_axioms                           reachable_all
% 7.25/1.47  --bmc1_min_bound                        0
% 7.25/1.47  --bmc1_max_bound                        -1
% 7.25/1.47  --bmc1_max_bound_default                -1
% 7.25/1.47  --bmc1_symbol_reachability              true
% 7.25/1.47  --bmc1_property_lemmas                  false
% 7.25/1.47  --bmc1_k_induction                      false
% 7.25/1.47  --bmc1_non_equiv_states                 false
% 7.25/1.47  --bmc1_deadlock                         false
% 7.25/1.47  --bmc1_ucm                              false
% 7.25/1.47  --bmc1_add_unsat_core                   none
% 7.25/1.47  --bmc1_unsat_core_children              false
% 7.25/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.25/1.47  --bmc1_out_stat                         full
% 7.25/1.47  --bmc1_ground_init                      false
% 7.25/1.47  --bmc1_pre_inst_next_state              false
% 7.25/1.47  --bmc1_pre_inst_state                   false
% 7.25/1.47  --bmc1_pre_inst_reach_state             false
% 7.25/1.47  --bmc1_out_unsat_core                   false
% 7.25/1.47  --bmc1_aig_witness_out                  false
% 7.25/1.47  --bmc1_verbose                          false
% 7.25/1.47  --bmc1_dump_clauses_tptp                false
% 7.25/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.25/1.47  --bmc1_dump_file                        -
% 7.25/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.25/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.25/1.47  --bmc1_ucm_extend_mode                  1
% 7.25/1.47  --bmc1_ucm_init_mode                    2
% 7.25/1.47  --bmc1_ucm_cone_mode                    none
% 7.25/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.25/1.47  --bmc1_ucm_relax_model                  4
% 7.25/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.25/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.25/1.47  --bmc1_ucm_layered_model                none
% 7.25/1.47  --bmc1_ucm_max_lemma_size               10
% 7.25/1.47  
% 7.25/1.47  ------ AIG Options
% 7.25/1.47  
% 7.25/1.47  --aig_mode                              false
% 7.25/1.47  
% 7.25/1.47  ------ Instantiation Options
% 7.25/1.47  
% 7.25/1.47  --instantiation_flag                    true
% 7.25/1.47  --inst_sos_flag                         false
% 7.25/1.47  --inst_sos_phase                        true
% 7.25/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.25/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.25/1.47  --inst_lit_sel_side                     none
% 7.25/1.47  --inst_solver_per_active                1400
% 7.25/1.47  --inst_solver_calls_frac                1.
% 7.25/1.47  --inst_passive_queue_type               priority_queues
% 7.25/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.25/1.47  --inst_passive_queues_freq              [25;2]
% 7.25/1.47  --inst_dismatching                      true
% 7.25/1.47  --inst_eager_unprocessed_to_passive     true
% 7.25/1.47  --inst_prop_sim_given                   true
% 7.25/1.47  --inst_prop_sim_new                     false
% 7.25/1.47  --inst_subs_new                         false
% 7.25/1.47  --inst_eq_res_simp                      false
% 7.25/1.47  --inst_subs_given                       false
% 7.25/1.47  --inst_orphan_elimination               true
% 7.25/1.47  --inst_learning_loop_flag               true
% 7.25/1.47  --inst_learning_start                   3000
% 7.25/1.47  --inst_learning_factor                  2
% 7.25/1.47  --inst_start_prop_sim_after_learn       3
% 7.25/1.47  --inst_sel_renew                        solver
% 7.25/1.47  --inst_lit_activity_flag                true
% 7.25/1.47  --inst_restr_to_given                   false
% 7.25/1.47  --inst_activity_threshold               500
% 7.25/1.47  --inst_out_proof                        true
% 7.25/1.47  
% 7.25/1.47  ------ Resolution Options
% 7.25/1.47  
% 7.25/1.47  --resolution_flag                       false
% 7.25/1.47  --res_lit_sel                           adaptive
% 7.25/1.47  --res_lit_sel_side                      none
% 7.25/1.47  --res_ordering                          kbo
% 7.25/1.47  --res_to_prop_solver                    active
% 7.25/1.47  --res_prop_simpl_new                    false
% 7.25/1.47  --res_prop_simpl_given                  true
% 7.25/1.47  --res_passive_queue_type                priority_queues
% 7.25/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.25/1.47  --res_passive_queues_freq               [15;5]
% 7.25/1.47  --res_forward_subs                      full
% 7.25/1.47  --res_backward_subs                     full
% 7.25/1.47  --res_forward_subs_resolution           true
% 7.25/1.47  --res_backward_subs_resolution          true
% 7.25/1.47  --res_orphan_elimination                true
% 7.25/1.47  --res_time_limit                        2.
% 7.25/1.47  --res_out_proof                         true
% 7.25/1.47  
% 7.25/1.47  ------ Superposition Options
% 7.25/1.47  
% 7.25/1.47  --superposition_flag                    true
% 7.25/1.47  --sup_passive_queue_type                priority_queues
% 7.25/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.25/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.25/1.47  --demod_completeness_check              fast
% 7.25/1.47  --demod_use_ground                      true
% 7.25/1.47  --sup_to_prop_solver                    passive
% 7.25/1.47  --sup_prop_simpl_new                    true
% 7.25/1.47  --sup_prop_simpl_given                  true
% 7.25/1.47  --sup_fun_splitting                     false
% 7.25/1.47  --sup_smt_interval                      50000
% 7.25/1.47  
% 7.25/1.47  ------ Superposition Simplification Setup
% 7.25/1.47  
% 7.25/1.47  --sup_indices_passive                   []
% 7.25/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.25/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.25/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.47  --sup_full_bw                           [BwDemod]
% 7.25/1.47  --sup_immed_triv                        [TrivRules]
% 7.25/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.25/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.47  --sup_immed_bw_main                     []
% 7.25/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.25/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.25/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.25/1.47  
% 7.25/1.47  ------ Combination Options
% 7.25/1.47  
% 7.25/1.47  --comb_res_mult                         3
% 7.25/1.47  --comb_sup_mult                         2
% 7.25/1.47  --comb_inst_mult                        10
% 7.25/1.47  
% 7.25/1.47  ------ Debug Options
% 7.25/1.47  
% 7.25/1.47  --dbg_backtrace                         false
% 7.25/1.47  --dbg_dump_prop_clauses                 false
% 7.25/1.47  --dbg_dump_prop_clauses_file            -
% 7.25/1.47  --dbg_out_stat                          false
% 7.25/1.47  
% 7.25/1.47  
% 7.25/1.47  
% 7.25/1.47  
% 7.25/1.47  ------ Proving...
% 7.25/1.47  
% 7.25/1.47  
% 7.25/1.47  % SZS status Theorem for theBenchmark.p
% 7.25/1.47  
% 7.25/1.47   Resolution empty clause
% 7.25/1.47  
% 7.25/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.25/1.47  
% 7.25/1.47  fof(f17,axiom,(
% 7.25/1.47    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 7.25/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.47  
% 7.25/1.47  fof(f23,plain,(
% 7.25/1.47    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 7.25/1.47    inference(ennf_transformation,[],[f17])).
% 7.25/1.47  
% 7.25/1.47  fof(f28,plain,(
% 7.25/1.47    ! [X5,X4,X3,X2,X1,X0,X6] : (sP2(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 7.25/1.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 7.25/1.47  
% 7.25/1.47  fof(f29,plain,(
% 7.25/1.47    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP2(X5,X4,X3,X2,X1,X0,X6))),
% 7.25/1.47    inference(definition_folding,[],[f23,f28])).
% 7.25/1.47  
% 7.25/1.47  fof(f46,plain,(
% 7.25/1.47    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP2(X5,X4,X3,X2,X1,X0,X6)) & (sP2(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 7.25/1.47    inference(nnf_transformation,[],[f29])).
% 7.25/1.47  
% 7.25/1.47  fof(f99,plain,(
% 7.25/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP2(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 7.25/1.47    inference(cnf_transformation,[],[f46])).
% 7.25/1.47  
% 7.25/1.47  fof(f10,axiom,(
% 7.25/1.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.25/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.47  
% 7.25/1.47  fof(f74,plain,(
% 7.25/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.25/1.47    inference(cnf_transformation,[],[f10])).
% 7.25/1.47  
% 7.25/1.47  fof(f11,axiom,(
% 7.25/1.47    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.25/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.47  
% 7.25/1.47  fof(f75,plain,(
% 7.25/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.25/1.47    inference(cnf_transformation,[],[f11])).
% 7.25/1.47  
% 7.25/1.47  fof(f105,plain,(
% 7.25/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.25/1.47    inference(definition_unfolding,[],[f74,f75])).
% 7.25/1.47  
% 7.25/1.47  fof(f116,plain,(
% 7.25/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP2(X5,X4,X3,X2,X1,X0,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 7.25/1.47    inference(definition_unfolding,[],[f99,f105])).
% 7.25/1.47  
% 7.25/1.47  fof(f133,plain,(
% 7.25/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (sP2(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 7.25/1.47    inference(equality_resolution,[],[f116])).
% 7.25/1.47  
% 7.25/1.47  fof(f41,plain,(
% 7.25/1.47    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP2(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP2(X5,X4,X3,X2,X1,X0,X6)))),
% 7.25/1.47    inference(nnf_transformation,[],[f28])).
% 7.25/1.47  
% 7.25/1.47  fof(f42,plain,(
% 7.25/1.47    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP2(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP2(X5,X4,X3,X2,X1,X0,X6)))),
% 7.25/1.47    inference(flattening,[],[f41])).
% 7.25/1.47  
% 7.25/1.47  fof(f43,plain,(
% 7.25/1.47    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP2(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP2(X0,X1,X2,X3,X4,X5,X6)))),
% 7.25/1.47    inference(rectify,[],[f42])).
% 7.25/1.47  
% 7.25/1.47  fof(f44,plain,(
% 7.25/1.47    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK4(X0,X1,X2,X3,X4,X5,X6) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK4(X0,X1,X2,X3,X4,X5,X6) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 7.25/1.47    introduced(choice_axiom,[])).
% 7.25/1.47  
% 7.25/1.47  fof(f45,plain,(
% 7.25/1.47    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP2(X0,X1,X2,X3,X4,X5,X6) | (((sK4(X0,X1,X2,X3,X4,X5,X6) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK4(X0,X1,X2,X3,X4,X5,X6) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP2(X0,X1,X2,X3,X4,X5,X6)))),
% 7.25/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 7.25/1.47  
% 7.25/1.47  fof(f86,plain,(
% 7.25/1.47    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | ~sP2(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.25/1.47    inference(cnf_transformation,[],[f45])).
% 7.25/1.47  
% 7.25/1.47  fof(f132,plain,(
% 7.25/1.47    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | ~sP2(X0,X1,X2,X3,X4,X8,X6)) )),
% 7.25/1.47    inference(equality_resolution,[],[f86])).
% 7.25/1.47  
% 7.25/1.47  fof(f91,plain,(
% 7.25/1.47    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X0 != X8 | ~sP2(X0,X1,X2,X3,X4,X5,X6)) )),
% 7.25/1.47    inference(cnf_transformation,[],[f45])).
% 7.25/1.47  
% 7.25/1.47  fof(f127,plain,(
% 7.25/1.47    ( ! [X6,X4,X2,X8,X5,X3,X1] : (r2_hidden(X8,X6) | ~sP2(X8,X1,X2,X3,X4,X5,X6)) )),
% 7.25/1.47    inference(equality_resolution,[],[f91])).
% 7.25/1.47  
% 7.25/1.47  fof(f19,conjecture,(
% 7.25/1.47    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 7.25/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.47  
% 7.25/1.47  fof(f20,negated_conjecture,(
% 7.25/1.47    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 7.25/1.47    inference(negated_conjecture,[],[f19])).
% 7.25/1.47  
% 7.25/1.47  fof(f24,plain,(
% 7.25/1.47    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 7.25/1.47    inference(ennf_transformation,[],[f20])).
% 7.25/1.47  
% 7.25/1.47  fof(f48,plain,(
% 7.25/1.47    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK6,sK7) = X0) )),
% 7.25/1.47    introduced(choice_axiom,[])).
% 7.25/1.47  
% 7.25/1.47  fof(f47,plain,(
% 7.25/1.47    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK5) = sK5 | k1_mcart_1(sK5) = sK5) & ? [X2,X1] : k4_tarski(X1,X2) = sK5)),
% 7.25/1.47    introduced(choice_axiom,[])).
% 7.25/1.47  
% 7.25/1.47  fof(f49,plain,(
% 7.25/1.47    (k2_mcart_1(sK5) = sK5 | k1_mcart_1(sK5) = sK5) & k4_tarski(sK6,sK7) = sK5),
% 7.25/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f24,f48,f47])).
% 7.25/1.47  
% 7.25/1.47  fof(f104,plain,(
% 7.25/1.47    k2_mcart_1(sK5) = sK5 | k1_mcart_1(sK5) = sK5),
% 7.25/1.47    inference(cnf_transformation,[],[f49])).
% 7.25/1.47  
% 7.25/1.47  fof(f103,plain,(
% 7.25/1.47    k4_tarski(sK6,sK7) = sK5),
% 7.25/1.47    inference(cnf_transformation,[],[f49])).
% 7.25/1.47  
% 7.25/1.47  fof(f18,axiom,(
% 7.25/1.47    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 7.25/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.47  
% 7.25/1.47  fof(f101,plain,(
% 7.25/1.47    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 7.25/1.47    inference(cnf_transformation,[],[f18])).
% 7.25/1.47  
% 7.25/1.47  fof(f102,plain,(
% 7.25/1.47    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 7.25/1.47    inference(cnf_transformation,[],[f18])).
% 7.25/1.47  
% 7.25/1.47  fof(f14,axiom,(
% 7.25/1.47    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 7.25/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.47  
% 7.25/1.47  fof(f39,plain,(
% 7.25/1.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.25/1.47    inference(nnf_transformation,[],[f14])).
% 7.25/1.47  
% 7.25/1.47  fof(f40,plain,(
% 7.25/1.47    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 7.25/1.47    inference(flattening,[],[f39])).
% 7.25/1.47  
% 7.25/1.47  fof(f81,plain,(
% 7.25/1.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 7.25/1.47    inference(cnf_transformation,[],[f40])).
% 7.25/1.47  
% 7.25/1.47  fof(f80,plain,(
% 7.25/1.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 7.25/1.47    inference(cnf_transformation,[],[f40])).
% 7.25/1.47  
% 7.25/1.47  fof(f12,axiom,(
% 7.25/1.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.25/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.47  
% 7.25/1.47  fof(f38,plain,(
% 7.25/1.47    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.25/1.47    inference(nnf_transformation,[],[f12])).
% 7.25/1.48  
% 7.25/1.48  fof(f77,plain,(
% 7.25/1.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f38])).
% 7.25/1.48  
% 7.25/1.48  fof(f5,axiom,(
% 7.25/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f69,plain,(
% 7.25/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f5])).
% 7.25/1.48  
% 7.25/1.48  fof(f6,axiom,(
% 7.25/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f70,plain,(
% 7.25/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f6])).
% 7.25/1.48  
% 7.25/1.48  fof(f7,axiom,(
% 7.25/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f71,plain,(
% 7.25/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f7])).
% 7.25/1.48  
% 7.25/1.48  fof(f8,axiom,(
% 7.25/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f72,plain,(
% 7.25/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f8])).
% 7.25/1.48  
% 7.25/1.48  fof(f9,axiom,(
% 7.25/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f73,plain,(
% 7.25/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f9])).
% 7.25/1.48  
% 7.25/1.48  fof(f106,plain,(
% 7.25/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.25/1.48    inference(definition_unfolding,[],[f73,f105])).
% 7.25/1.48  
% 7.25/1.48  fof(f107,plain,(
% 7.25/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.25/1.48    inference(definition_unfolding,[],[f72,f106])).
% 7.25/1.48  
% 7.25/1.48  fof(f108,plain,(
% 7.25/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.25/1.48    inference(definition_unfolding,[],[f71,f107])).
% 7.25/1.48  
% 7.25/1.48  fof(f109,plain,(
% 7.25/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.25/1.48    inference(definition_unfolding,[],[f70,f108])).
% 7.25/1.48  
% 7.25/1.48  fof(f110,plain,(
% 7.25/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.25/1.48    inference(definition_unfolding,[],[f69,f109])).
% 7.25/1.48  
% 7.25/1.48  fof(f111,plain,(
% 7.25/1.48    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.25/1.48    inference(definition_unfolding,[],[f77,f110])).
% 7.25/1.48  
% 7.25/1.48  fof(f15,axiom,(
% 7.25/1.48    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f22,plain,(
% 7.25/1.48    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 7.25/1.48    inference(ennf_transformation,[],[f15])).
% 7.25/1.48  
% 7.25/1.48  fof(f83,plain,(
% 7.25/1.48    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 7.25/1.48    inference(cnf_transformation,[],[f22])).
% 7.25/1.48  
% 7.25/1.48  fof(f1,axiom,(
% 7.25/1.48    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f50,plain,(
% 7.25/1.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f1])).
% 7.25/1.48  
% 7.25/1.48  fof(f16,axiom,(
% 7.25/1.48    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f84,plain,(
% 7.25/1.48    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f16])).
% 7.25/1.48  
% 7.25/1.48  fof(f3,axiom,(
% 7.25/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f52,plain,(
% 7.25/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.25/1.48    inference(cnf_transformation,[],[f3])).
% 7.25/1.48  
% 7.25/1.48  fof(f114,plain,(
% 7.25/1.48    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 7.25/1.48    inference(definition_unfolding,[],[f84,f52,f110])).
% 7.25/1.48  
% 7.25/1.48  fof(f2,axiom,(
% 7.25/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.25/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.25/1.48  
% 7.25/1.48  fof(f51,plain,(
% 7.25/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.25/1.48    inference(cnf_transformation,[],[f2])).
% 7.25/1.48  
% 7.25/1.48  fof(f82,plain,(
% 7.25/1.48    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 7.25/1.48    inference(cnf_transformation,[],[f22])).
% 7.25/1.48  
% 7.25/1.48  cnf(c_42,plain,
% 7.25/1.48      ( sP2(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
% 7.25/1.48      inference(cnf_transformation,[],[f133]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3237,plain,
% 7.25/1.48      ( sP2(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_39,plain,
% 7.25/1.48      ( ~ sP2(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X5,X6) ),
% 7.25/1.48      inference(cnf_transformation,[],[f132]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3240,plain,
% 7.25/1.48      ( sP2(X0,X1,X2,X3,X4,X5,X6) != iProver_top
% 7.25/1.48      | r2_hidden(X5,X6) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_5241,plain,
% 7.25/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_3237,c_3240]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_34,plain,
% 7.25/1.48      ( ~ sP2(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X0,X6) ),
% 7.25/1.48      inference(cnf_transformation,[],[f127]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3245,plain,
% 7.25/1.48      ( sP2(X0,X1,X2,X3,X4,X5,X6) != iProver_top
% 7.25/1.48      | r2_hidden(X0,X6) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_5236,plain,
% 7.25/1.48      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X0)) = iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_3237,c_3245]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_45,negated_conjecture,
% 7.25/1.48      ( k1_mcart_1(sK5) = sK5 | k2_mcart_1(sK5) = sK5 ),
% 7.25/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_46,negated_conjecture,
% 7.25/1.48      ( k4_tarski(sK6,sK7) = sK5 ),
% 7.25/1.48      inference(cnf_transformation,[],[f103]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_44,plain,
% 7.25/1.48      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 7.25/1.48      inference(cnf_transformation,[],[f101]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3591,plain,
% 7.25/1.48      ( k1_mcart_1(sK5) = sK6 ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_46,c_44]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3593,plain,
% 7.25/1.48      ( k2_mcart_1(sK5) = sK5 | sK6 = sK5 ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_45,c_3591]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_43,plain,
% 7.25/1.48      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 7.25/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3585,plain,
% 7.25/1.48      ( k2_mcart_1(sK5) = sK7 ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_46,c_43]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3595,plain,
% 7.25/1.48      ( sK7 = sK5 | sK6 = sK5 ),
% 7.25/1.48      inference(demodulation,[status(thm)],[c_3593,c_3585]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3736,plain,
% 7.25/1.48      ( k4_tarski(sK6,sK5) = sK5 | sK6 = sK5 ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_3595,c_46]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_21,plain,
% 7.25/1.48      ( ~ r2_hidden(X0,X1)
% 7.25/1.48      | ~ r2_hidden(X2,X3)
% 7.25/1.48      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.25/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3257,plain,
% 7.25/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.25/1.48      | r2_hidden(X2,X3) != iProver_top
% 7.25/1.48      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_5098,plain,
% 7.25/1.48      ( sK6 = sK5
% 7.25/1.48      | r2_hidden(sK6,X0) != iProver_top
% 7.25/1.48      | r2_hidden(sK5,X1) != iProver_top
% 7.25/1.48      | r2_hidden(sK5,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_3736,c_3257]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_22,plain,
% 7.25/1.48      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 7.25/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3256,plain,
% 7.25/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.25/1.48      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3926,plain,
% 7.25/1.48      ( r2_hidden(sK7,X0) = iProver_top
% 7.25/1.48      | r2_hidden(sK5,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_46,c_3256]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_5656,plain,
% 7.25/1.48      ( sK6 = sK5
% 7.25/1.48      | r2_hidden(sK7,X0) = iProver_top
% 7.25/1.48      | r2_hidden(sK6,X1) != iProver_top
% 7.25/1.48      | r2_hidden(sK5,X0) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_5098,c_3926]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_6533,plain,
% 7.25/1.48      ( sK6 = sK5
% 7.25/1.48      | r2_hidden(sK7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,sK5)) = iProver_top
% 7.25/1.48      | r2_hidden(sK6,X5) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_5236,c_5656]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_7599,plain,
% 7.25/1.48      ( sK6 = sK5
% 7.25/1.48      | r2_hidden(sK7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,sK5)) = iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_5236,c_6533]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_5097,plain,
% 7.25/1.48      ( r2_hidden(sK7,X0) != iProver_top
% 7.25/1.48      | r2_hidden(sK6,X1) != iProver_top
% 7.25/1.48      | r2_hidden(sK5,k2_zfmisc_1(X1,X0)) = iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_46,c_3257]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_18,plain,
% 7.25/1.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 7.25/1.48      | ~ r2_hidden(X0,X1) ),
% 7.25/1.48      inference(cnf_transformation,[],[f111]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3259,plain,
% 7.25/1.48      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 7.25/1.48      | r2_hidden(X0,X1) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_24,plain,
% 7.25/1.48      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 7.25/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3254,plain,
% 7.25/1.48      ( k1_xboole_0 = X0 | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_5410,plain,
% 7.25/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 7.25/1.48      | r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_3259,c_3254]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_0,plain,
% 7.25/1.48      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.25/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_26,plain,
% 7.25/1.48      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k1_xboole_0 ),
% 7.25/1.48      inference(cnf_transformation,[],[f114]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3610,plain,
% 7.25/1.48      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != k1_xboole_0 ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_0,c_26]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_1,plain,
% 7.25/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.25/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3611,plain,
% 7.25/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 7.25/1.48      inference(demodulation,[status(thm)],[c_3610,c_1]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_20482,plain,
% 7.25/1.48      ( r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 7.25/1.48      inference(global_propositional_subsumption,[status(thm)],[c_5410,c_3611]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_20491,plain,
% 7.25/1.48      ( r2_hidden(sK7,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 7.25/1.48      | r2_hidden(sK6,X0) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_5097,c_20482]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_20983,plain,
% 7.25/1.48      ( sK6 = sK5 | r2_hidden(sK6,X0) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_7599,c_20491]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_21000,plain,
% 7.25/1.48      ( sK6 = sK5 ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_5241,c_20983]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_21483,plain,
% 7.25/1.48      ( r2_hidden(sK7,X0) != iProver_top
% 7.25/1.48      | r2_hidden(sK5,X1) != iProver_top
% 7.25/1.48      | r2_hidden(sK5,k2_zfmisc_1(X1,X0)) = iProver_top ),
% 7.25/1.48      inference(demodulation,[status(thm)],[c_21000,c_5097]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_25,plain,
% 7.25/1.48      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 7.25/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_3253,plain,
% 7.25/1.48      ( k1_xboole_0 = X0 | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.25/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_5411,plain,
% 7.25/1.48      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_xboole_0
% 7.25/1.48      | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_3259,c_3253]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_22085,plain,
% 7.25/1.48      ( r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) != iProver_top ),
% 7.25/1.48      inference(global_propositional_subsumption,[status(thm)],[c_5411,c_3611]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_22093,plain,
% 7.25/1.48      ( r2_hidden(sK7,X0) != iProver_top
% 7.25/1.48      | r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_21483,c_22085]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_22232,plain,
% 7.25/1.48      ( r2_hidden(sK7,X0) != iProver_top ),
% 7.25/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_22093,c_5236]) ).
% 7.25/1.48  
% 7.25/1.48  cnf(c_22236,plain,
% 7.25/1.48      ( $false ),
% 7.25/1.48      inference(superposition,[status(thm)],[c_5241,c_22232]) ).
% 7.25/1.48  
% 7.25/1.48  
% 7.25/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.25/1.48  
% 7.25/1.48  ------                               Statistics
% 7.25/1.48  
% 7.25/1.48  ------ General
% 7.25/1.48  
% 7.25/1.48  abstr_ref_over_cycles:                  0
% 7.25/1.48  abstr_ref_under_cycles:                 0
% 7.25/1.48  gc_basic_clause_elim:                   0
% 7.25/1.48  forced_gc_time:                         0
% 7.25/1.48  parsing_time:                           0.013
% 7.25/1.48  unif_index_cands_time:                  0.
% 7.25/1.48  unif_index_add_time:                    0.
% 7.25/1.48  orderings_time:                         0.
% 7.25/1.48  out_proof_time:                         0.01
% 7.25/1.48  total_time:                             0.906
% 7.25/1.48  num_of_symbols:                         51
% 7.25/1.48  num_of_terms:                           34277
% 7.25/1.48  
% 7.25/1.48  ------ Preprocessing
% 7.25/1.48  
% 7.25/1.48  num_of_splits:                          0
% 7.25/1.48  num_of_split_atoms:                     0
% 7.25/1.48  num_of_reused_defs:                     0
% 7.25/1.48  num_eq_ax_congr_red:                    120
% 7.25/1.48  num_of_sem_filtered_clauses:            1
% 7.25/1.48  num_of_subtypes:                        0
% 7.25/1.48  monotx_restored_types:                  0
% 7.25/1.48  sat_num_of_epr_types:                   0
% 7.25/1.48  sat_num_of_non_cyclic_types:            0
% 7.25/1.48  sat_guarded_non_collapsed_types:        0
% 7.25/1.48  num_pure_diseq_elim:                    0
% 7.25/1.48  simp_replaced_by:                       0
% 7.25/1.48  res_preprocessed:                       168
% 7.25/1.48  prep_upred:                             0
% 7.25/1.48  prep_unflattend:                        421
% 7.25/1.48  smt_new_axioms:                         0
% 7.25/1.48  pred_elim_cands:                        5
% 7.25/1.48  pred_elim:                              0
% 7.25/1.48  pred_elim_cl:                           0
% 7.25/1.48  pred_elim_cycles:                       4
% 7.25/1.48  merged_defs:                            6
% 7.25/1.48  merged_defs_ncl:                        0
% 7.25/1.48  bin_hyper_res:                          6
% 7.25/1.48  prep_cycles:                            3
% 7.25/1.48  pred_elim_time:                         0.033
% 7.25/1.48  splitting_time:                         0.
% 7.25/1.48  sem_filter_time:                        0.
% 7.25/1.48  monotx_time:                            0.001
% 7.25/1.48  subtype_inf_time:                       0.
% 7.25/1.48  
% 7.25/1.48  ------ Problem properties
% 7.25/1.48  
% 7.25/1.48  clauses:                                47
% 7.25/1.48  conjectures:                            2
% 7.25/1.48  epr:                                    19
% 7.25/1.48  horn:                                   42
% 7.25/1.48  ground:                                 2
% 7.25/1.48  unary:                                  18
% 7.25/1.48  binary:                                 15
% 7.25/1.48  lits:                                   107
% 7.25/1.48  lits_eq:                                40
% 7.25/1.48  fd_pure:                                0
% 7.25/1.48  fd_pseudo:                              0
% 7.25/1.48  fd_cond:                                2
% 7.25/1.48  fd_pseudo_cond:                         4
% 7.25/1.48  ac_symbols:                             0
% 7.25/1.48  
% 7.25/1.48  ------ Propositional Solver
% 7.25/1.48  
% 7.25/1.48  prop_solver_calls:                      26
% 7.25/1.48  prop_fast_solver_calls:                 1493
% 7.25/1.48  smt_solver_calls:                       0
% 7.25/1.48  smt_fast_solver_calls:                  0
% 7.25/1.48  prop_num_of_clauses:                    7532
% 7.25/1.48  prop_preprocess_simplified:             28733
% 7.25/1.48  prop_fo_subsumed:                       2
% 7.25/1.48  prop_solver_time:                       0.
% 7.25/1.48  smt_solver_time:                        0.
% 7.25/1.48  smt_fast_solver_time:                   0.
% 7.25/1.48  prop_fast_solver_time:                  0.
% 7.25/1.48  prop_unsat_core_time:                   0.
% 7.25/1.48  
% 7.25/1.48  ------ QBF
% 7.25/1.48  
% 7.25/1.48  qbf_q_res:                              0
% 7.25/1.48  qbf_num_tautologies:                    0
% 7.25/1.48  qbf_prep_cycles:                        0
% 7.25/1.48  
% 7.25/1.48  ------ BMC1
% 7.25/1.48  
% 7.25/1.48  bmc1_current_bound:                     -1
% 7.25/1.48  bmc1_last_solved_bound:                 -1
% 7.25/1.48  bmc1_unsat_core_size:                   -1
% 7.25/1.48  bmc1_unsat_core_parents_size:           -1
% 7.25/1.48  bmc1_merge_next_fun:                    0
% 7.25/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.25/1.48  
% 7.25/1.48  ------ Instantiation
% 7.25/1.48  
% 7.25/1.48  inst_num_of_clauses:                    3031
% 7.25/1.48  inst_num_in_passive:                    1547
% 7.25/1.48  inst_num_in_active:                     645
% 7.25/1.48  inst_num_in_unprocessed:                839
% 7.25/1.48  inst_num_of_loops:                      730
% 7.25/1.48  inst_num_of_learning_restarts:          0
% 7.25/1.48  inst_num_moves_active_passive:          83
% 7.25/1.48  inst_lit_activity:                      0
% 7.25/1.48  inst_lit_activity_moves:                1
% 7.25/1.48  inst_num_tautologies:                   0
% 7.25/1.48  inst_num_prop_implied:                  0
% 7.25/1.48  inst_num_existing_simplified:           0
% 7.25/1.48  inst_num_eq_res_simplified:             0
% 7.25/1.48  inst_num_child_elim:                    0
% 7.25/1.48  inst_num_of_dismatching_blockings:      1248
% 7.25/1.48  inst_num_of_non_proper_insts:           2891
% 7.25/1.48  inst_num_of_duplicates:                 0
% 7.25/1.48  inst_inst_num_from_inst_to_res:         0
% 7.25/1.48  inst_dismatching_checking_time:         0.
% 7.25/1.48  
% 7.25/1.48  ------ Resolution
% 7.25/1.48  
% 7.25/1.48  res_num_of_clauses:                     0
% 7.25/1.48  res_num_in_passive:                     0
% 7.25/1.48  res_num_in_active:                      0
% 7.25/1.48  res_num_of_loops:                       171
% 7.25/1.48  res_forward_subset_subsumed:            74
% 7.25/1.48  res_backward_subset_subsumed:           0
% 7.25/1.48  res_forward_subsumed:                   0
% 7.25/1.48  res_backward_subsumed:                  0
% 7.25/1.48  res_forward_subsumption_resolution:     0
% 7.25/1.48  res_backward_subsumption_resolution:    0
% 7.25/1.48  res_clause_to_clause_subsumption:       3558
% 7.25/1.48  res_orphan_elimination:                 0
% 7.25/1.48  res_tautology_del:                      115
% 7.25/1.48  res_num_eq_res_simplified:              0
% 7.25/1.48  res_num_sel_changes:                    0
% 7.25/1.48  res_moves_from_active_to_pass:          0
% 7.25/1.48  
% 7.25/1.48  ------ Superposition
% 7.25/1.48  
% 7.25/1.48  sup_time_total:                         0.
% 7.25/1.48  sup_time_generating:                    0.
% 7.25/1.48  sup_time_sim_full:                      0.
% 7.25/1.48  sup_time_sim_immed:                     0.
% 7.25/1.48  
% 7.25/1.48  sup_num_of_clauses:                     94
% 7.25/1.48  sup_num_in_active:                      85
% 7.25/1.48  sup_num_in_passive:                     9
% 7.25/1.48  sup_num_of_loops:                       145
% 7.25/1.48  sup_fw_superposition:                   262
% 7.25/1.48  sup_bw_superposition:                   179
% 7.25/1.48  sup_immediate_simplified:               54
% 7.25/1.48  sup_given_eliminated:                   0
% 7.25/1.48  comparisons_done:                       0
% 7.25/1.48  comparisons_avoided:                    0
% 7.25/1.48  
% 7.25/1.48  ------ Simplifications
% 7.25/1.48  
% 7.25/1.48  
% 7.25/1.48  sim_fw_subset_subsumed:                 5
% 7.25/1.48  sim_bw_subset_subsumed:                 75
% 7.25/1.48  sim_fw_subsumed:                        35
% 7.25/1.48  sim_bw_subsumed:                        0
% 7.25/1.48  sim_fw_subsumption_res:                 1
% 7.25/1.48  sim_bw_subsumption_res:                 0
% 7.25/1.48  sim_tautology_del:                      10
% 7.25/1.48  sim_eq_tautology_del:                   8
% 7.25/1.48  sim_eq_res_simp:                        0
% 7.25/1.48  sim_fw_demodulated:                     2
% 7.25/1.48  sim_bw_demodulated:                     6
% 7.25/1.48  sim_light_normalised:                   0
% 7.25/1.48  sim_joinable_taut:                      0
% 7.25/1.48  sim_joinable_simp:                      0
% 7.25/1.48  sim_ac_normalised:                      0
% 7.25/1.48  sim_smt_subsumption:                    0
% 7.25/1.48  
%------------------------------------------------------------------------------
