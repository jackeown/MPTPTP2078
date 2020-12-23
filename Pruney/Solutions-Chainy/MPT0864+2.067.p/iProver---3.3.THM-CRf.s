%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:58 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 646 expanded)
%              Number of clauses        :   40 (  72 expanded)
%              Number of leaves         :   22 ( 203 expanded)
%              Depth                    :   16
%              Number of atoms          :  373 (1293 expanded)
%              Number of equality atoms :  303 (1154 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   34 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK3,sK4) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK2) = sK2
        | k1_mcart_1(sK2) = sK2 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK2 ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( k2_mcart_1(sK2) = sK2
      | k1_mcart_1(sK2) = sK2 )
    & k4_tarski(sK3,sK4) = sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f35,f34])).

fof(f77,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f75,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f82])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f81])).

fof(f92,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f53,f82,f85,f82])).

fof(f24,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8
                & X6 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | X6 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ( X0 != X8
              & X1 != X8
              & X2 != X8
              & X3 != X8
              & X4 != X8
              & X5 != X8
              & X6 != X8 )
            | ~ r2_hidden(X8,X7) )
          & ( X0 = X8
            | X1 = X8
            | X2 = X8
            | X3 = X8
            | X4 = X8
            | X5 = X8
            | X6 = X8
            | r2_hidden(X8,X7) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | X6 != X9
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | ~ sP0(X0,X1,X2,X3,X4,X5,X9,X7) ) ),
    inference(equality_resolution,[],[f56])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ),
    inference(definition_folding,[],[f22,f24])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) )
      & ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(definition_unfolding,[],[f71,f46])).

fof(f103,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP0(X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f94])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f83])).

fof(f90,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f51,f84,f85,f85,f85])).

fof(f95,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f83])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f54,f82,f82,f85])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_30,negated_conjecture,
    ( k1_mcart_1(sK2) = sK2
    | k2_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,negated_conjecture,
    ( k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4183,plain,
    ( k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_31,c_29])).

cnf(c_4194,plain,
    ( k2_mcart_1(sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_30,c_4183])).

cnf(c_28,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4180,plain,
    ( k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_31,c_28])).

cnf(c_4196,plain,
    ( sK4 = sK2
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_4194,c_4180])).

cnf(c_4199,plain,
    ( k4_tarski(sK3,sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_4196,c_31])).

cnf(c_9,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4427,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0))
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_4199,c_9])).

cnf(c_24,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | r2_hidden(X6,X7) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_27,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1585,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | X11 != X12
    | X13 != X14
    | k6_enumset1(X4,X4,X5,X7,X9,X11,X13,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_27])).

cnf(c_1586,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(unflattening,[status(thm)],[c_1585])).

cnf(c_1587,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1586])).

cnf(c_1589,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_7,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_0,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4102,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7,c_0,c_1])).

cnf(c_4131,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4102])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4306,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4310,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4306])).

cnf(c_4312,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4310])).

cnf(c_8,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4391,plain,
    ( k6_enumset1(k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),sK2) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_31,c_8])).

cnf(c_4642,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_31,c_4391])).

cnf(c_4786,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_4196,c_4642])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3971,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5179,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK3 = sK2
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4786,c_3971])).

cnf(c_6111,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4427,c_1589,c_4131,c_4312,c_5179])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3970,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5144,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4642,c_3970])).

cnf(c_5600,plain,
    ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5144,c_4102])).

cnf(c_6117,plain,
    ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6111,c_5600])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6117,c_4312,c_1589])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:12:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.97/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/1.01  
% 2.97/1.01  ------  iProver source info
% 2.97/1.01  
% 2.97/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.97/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/1.01  git: non_committed_changes: false
% 2.97/1.01  git: last_make_outside_of_git: false
% 2.97/1.01  
% 2.97/1.01  ------ 
% 2.97/1.01  
% 2.97/1.01  ------ Input Options
% 2.97/1.01  
% 2.97/1.01  --out_options                           all
% 2.97/1.01  --tptp_safe_out                         true
% 2.97/1.01  --problem_path                          ""
% 2.97/1.01  --include_path                          ""
% 2.97/1.01  --clausifier                            res/vclausify_rel
% 2.97/1.01  --clausifier_options                    --mode clausify
% 2.97/1.01  --stdin                                 false
% 2.97/1.01  --stats_out                             all
% 2.97/1.01  
% 2.97/1.01  ------ General Options
% 2.97/1.01  
% 2.97/1.01  --fof                                   false
% 2.97/1.01  --time_out_real                         305.
% 2.97/1.01  --time_out_virtual                      -1.
% 2.97/1.01  --symbol_type_check                     false
% 2.97/1.01  --clausify_out                          false
% 2.97/1.01  --sig_cnt_out                           false
% 2.97/1.01  --trig_cnt_out                          false
% 2.97/1.01  --trig_cnt_out_tolerance                1.
% 2.97/1.01  --trig_cnt_out_sk_spl                   false
% 2.97/1.01  --abstr_cl_out                          false
% 2.97/1.01  
% 2.97/1.01  ------ Global Options
% 2.97/1.01  
% 2.97/1.01  --schedule                              default
% 2.97/1.01  --add_important_lit                     false
% 2.97/1.01  --prop_solver_per_cl                    1000
% 2.97/1.01  --min_unsat_core                        false
% 2.97/1.01  --soft_assumptions                      false
% 2.97/1.01  --soft_lemma_size                       3
% 2.97/1.01  --prop_impl_unit_size                   0
% 2.97/1.01  --prop_impl_unit                        []
% 2.97/1.01  --share_sel_clauses                     true
% 2.97/1.01  --reset_solvers                         false
% 2.97/1.01  --bc_imp_inh                            [conj_cone]
% 2.97/1.01  --conj_cone_tolerance                   3.
% 2.97/1.01  --extra_neg_conj                        none
% 2.97/1.01  --large_theory_mode                     true
% 2.97/1.01  --prolific_symb_bound                   200
% 2.97/1.01  --lt_threshold                          2000
% 2.97/1.01  --clause_weak_htbl                      true
% 2.97/1.01  --gc_record_bc_elim                     false
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing Options
% 2.97/1.01  
% 2.97/1.01  --preprocessing_flag                    true
% 2.97/1.01  --time_out_prep_mult                    0.1
% 2.97/1.01  --splitting_mode                        input
% 2.97/1.01  --splitting_grd                         true
% 2.97/1.01  --splitting_cvd                         false
% 2.97/1.01  --splitting_cvd_svl                     false
% 2.97/1.01  --splitting_nvd                         32
% 2.97/1.01  --sub_typing                            true
% 2.97/1.01  --prep_gs_sim                           true
% 2.97/1.01  --prep_unflatten                        true
% 2.97/1.01  --prep_res_sim                          true
% 2.97/1.01  --prep_upred                            true
% 2.97/1.01  --prep_sem_filter                       exhaustive
% 2.97/1.01  --prep_sem_filter_out                   false
% 2.97/1.01  --pred_elim                             true
% 2.97/1.01  --res_sim_input                         true
% 2.97/1.01  --eq_ax_congr_red                       true
% 2.97/1.01  --pure_diseq_elim                       true
% 2.97/1.01  --brand_transform                       false
% 2.97/1.01  --non_eq_to_eq                          false
% 2.97/1.01  --prep_def_merge                        true
% 2.97/1.01  --prep_def_merge_prop_impl              false
% 2.97/1.01  --prep_def_merge_mbd                    true
% 2.97/1.01  --prep_def_merge_tr_red                 false
% 2.97/1.01  --prep_def_merge_tr_cl                  false
% 2.97/1.01  --smt_preprocessing                     true
% 2.97/1.01  --smt_ac_axioms                         fast
% 2.97/1.01  --preprocessed_out                      false
% 2.97/1.01  --preprocessed_stats                    false
% 2.97/1.01  
% 2.97/1.01  ------ Abstraction refinement Options
% 2.97/1.01  
% 2.97/1.01  --abstr_ref                             []
% 2.97/1.01  --abstr_ref_prep                        false
% 2.97/1.01  --abstr_ref_until_sat                   false
% 2.97/1.01  --abstr_ref_sig_restrict                funpre
% 2.97/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.01  --abstr_ref_under                       []
% 2.97/1.01  
% 2.97/1.01  ------ SAT Options
% 2.97/1.01  
% 2.97/1.01  --sat_mode                              false
% 2.97/1.01  --sat_fm_restart_options                ""
% 2.97/1.01  --sat_gr_def                            false
% 2.97/1.01  --sat_epr_types                         true
% 2.97/1.01  --sat_non_cyclic_types                  false
% 2.97/1.01  --sat_finite_models                     false
% 2.97/1.01  --sat_fm_lemmas                         false
% 2.97/1.01  --sat_fm_prep                           false
% 2.97/1.01  --sat_fm_uc_incr                        true
% 2.97/1.01  --sat_out_model                         small
% 2.97/1.01  --sat_out_clauses                       false
% 2.97/1.01  
% 2.97/1.01  ------ QBF Options
% 2.97/1.01  
% 2.97/1.01  --qbf_mode                              false
% 2.97/1.01  --qbf_elim_univ                         false
% 2.97/1.01  --qbf_dom_inst                          none
% 2.97/1.01  --qbf_dom_pre_inst                      false
% 2.97/1.01  --qbf_sk_in                             false
% 2.97/1.01  --qbf_pred_elim                         true
% 2.97/1.01  --qbf_split                             512
% 2.97/1.01  
% 2.97/1.01  ------ BMC1 Options
% 2.97/1.01  
% 2.97/1.01  --bmc1_incremental                      false
% 2.97/1.01  --bmc1_axioms                           reachable_all
% 2.97/1.01  --bmc1_min_bound                        0
% 2.97/1.01  --bmc1_max_bound                        -1
% 2.97/1.01  --bmc1_max_bound_default                -1
% 2.97/1.01  --bmc1_symbol_reachability              true
% 2.97/1.01  --bmc1_property_lemmas                  false
% 2.97/1.01  --bmc1_k_induction                      false
% 2.97/1.01  --bmc1_non_equiv_states                 false
% 2.97/1.01  --bmc1_deadlock                         false
% 2.97/1.01  --bmc1_ucm                              false
% 2.97/1.01  --bmc1_add_unsat_core                   none
% 2.97/1.01  --bmc1_unsat_core_children              false
% 2.97/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.01  --bmc1_out_stat                         full
% 2.97/1.01  --bmc1_ground_init                      false
% 2.97/1.01  --bmc1_pre_inst_next_state              false
% 2.97/1.01  --bmc1_pre_inst_state                   false
% 2.97/1.01  --bmc1_pre_inst_reach_state             false
% 2.97/1.01  --bmc1_out_unsat_core                   false
% 2.97/1.01  --bmc1_aig_witness_out                  false
% 2.97/1.01  --bmc1_verbose                          false
% 2.97/1.01  --bmc1_dump_clauses_tptp                false
% 2.97/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.01  --bmc1_dump_file                        -
% 2.97/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.01  --bmc1_ucm_extend_mode                  1
% 2.97/1.01  --bmc1_ucm_init_mode                    2
% 2.97/1.01  --bmc1_ucm_cone_mode                    none
% 2.97/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.01  --bmc1_ucm_relax_model                  4
% 2.97/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.01  --bmc1_ucm_layered_model                none
% 2.97/1.01  --bmc1_ucm_max_lemma_size               10
% 2.97/1.01  
% 2.97/1.01  ------ AIG Options
% 2.97/1.01  
% 2.97/1.01  --aig_mode                              false
% 2.97/1.01  
% 2.97/1.01  ------ Instantiation Options
% 2.97/1.01  
% 2.97/1.01  --instantiation_flag                    true
% 2.97/1.01  --inst_sos_flag                         false
% 2.97/1.01  --inst_sos_phase                        true
% 2.97/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel_side                     num_symb
% 2.97/1.01  --inst_solver_per_active                1400
% 2.97/1.01  --inst_solver_calls_frac                1.
% 2.97/1.01  --inst_passive_queue_type               priority_queues
% 2.97/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.01  --inst_passive_queues_freq              [25;2]
% 2.97/1.01  --inst_dismatching                      true
% 2.97/1.01  --inst_eager_unprocessed_to_passive     true
% 2.97/1.01  --inst_prop_sim_given                   true
% 2.97/1.01  --inst_prop_sim_new                     false
% 2.97/1.01  --inst_subs_new                         false
% 2.97/1.01  --inst_eq_res_simp                      false
% 2.97/1.01  --inst_subs_given                       false
% 2.97/1.01  --inst_orphan_elimination               true
% 2.97/1.01  --inst_learning_loop_flag               true
% 2.97/1.01  --inst_learning_start                   3000
% 2.97/1.01  --inst_learning_factor                  2
% 2.97/1.01  --inst_start_prop_sim_after_learn       3
% 2.97/1.01  --inst_sel_renew                        solver
% 2.97/1.01  --inst_lit_activity_flag                true
% 2.97/1.01  --inst_restr_to_given                   false
% 2.97/1.01  --inst_activity_threshold               500
% 2.97/1.01  --inst_out_proof                        true
% 2.97/1.01  
% 2.97/1.01  ------ Resolution Options
% 2.97/1.01  
% 2.97/1.01  --resolution_flag                       true
% 2.97/1.01  --res_lit_sel                           adaptive
% 2.97/1.01  --res_lit_sel_side                      none
% 2.97/1.01  --res_ordering                          kbo
% 2.97/1.01  --res_to_prop_solver                    active
% 2.97/1.01  --res_prop_simpl_new                    false
% 2.97/1.01  --res_prop_simpl_given                  true
% 2.97/1.01  --res_passive_queue_type                priority_queues
% 2.97/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.01  --res_passive_queues_freq               [15;5]
% 2.97/1.01  --res_forward_subs                      full
% 2.97/1.01  --res_backward_subs                     full
% 2.97/1.01  --res_forward_subs_resolution           true
% 2.97/1.01  --res_backward_subs_resolution          true
% 2.97/1.01  --res_orphan_elimination                true
% 2.97/1.01  --res_time_limit                        2.
% 2.97/1.01  --res_out_proof                         true
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Options
% 2.97/1.01  
% 2.97/1.01  --superposition_flag                    true
% 2.97/1.01  --sup_passive_queue_type                priority_queues
% 2.97/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.01  --demod_completeness_check              fast
% 2.97/1.01  --demod_use_ground                      true
% 2.97/1.01  --sup_to_prop_solver                    passive
% 2.97/1.01  --sup_prop_simpl_new                    true
% 2.97/1.01  --sup_prop_simpl_given                  true
% 2.97/1.01  --sup_fun_splitting                     false
% 2.97/1.01  --sup_smt_interval                      50000
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Simplification Setup
% 2.97/1.01  
% 2.97/1.01  --sup_indices_passive                   []
% 2.97/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_full_bw                           [BwDemod]
% 2.97/1.01  --sup_immed_triv                        [TrivRules]
% 2.97/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_immed_bw_main                     []
% 2.97/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  
% 2.97/1.01  ------ Combination Options
% 2.97/1.01  
% 2.97/1.01  --comb_res_mult                         3
% 2.97/1.01  --comb_sup_mult                         2
% 2.97/1.01  --comb_inst_mult                        10
% 2.97/1.01  
% 2.97/1.01  ------ Debug Options
% 2.97/1.01  
% 2.97/1.01  --dbg_backtrace                         false
% 2.97/1.01  --dbg_dump_prop_clauses                 false
% 2.97/1.01  --dbg_dump_prop_clauses_file            -
% 2.97/1.01  --dbg_out_stat                          false
% 2.97/1.01  ------ Parsing...
% 2.97/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/1.01  ------ Proving...
% 2.97/1.01  ------ Problem Properties 
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  clauses                                 32
% 2.97/1.01  conjectures                             2
% 2.97/1.01  EPR                                     8
% 2.97/1.01  Horn                                    28
% 2.97/1.01  unary                                   9
% 2.97/1.01  binary                                  14
% 2.97/1.01  lits                                    76
% 2.97/1.01  lits eq                                 36
% 2.97/1.01  fd_pure                                 0
% 2.97/1.01  fd_pseudo                               0
% 2.97/1.01  fd_cond                                 2
% 2.97/1.01  fd_pseudo_cond                          3
% 2.97/1.01  AC symbols                              0
% 2.97/1.01  
% 2.97/1.01  ------ Schedule dynamic 5 is on 
% 2.97/1.01  
% 2.97/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  ------ 
% 2.97/1.01  Current options:
% 2.97/1.01  ------ 
% 2.97/1.01  
% 2.97/1.01  ------ Input Options
% 2.97/1.01  
% 2.97/1.01  --out_options                           all
% 2.97/1.01  --tptp_safe_out                         true
% 2.97/1.01  --problem_path                          ""
% 2.97/1.01  --include_path                          ""
% 2.97/1.01  --clausifier                            res/vclausify_rel
% 2.97/1.01  --clausifier_options                    --mode clausify
% 2.97/1.01  --stdin                                 false
% 2.97/1.01  --stats_out                             all
% 2.97/1.01  
% 2.97/1.01  ------ General Options
% 2.97/1.01  
% 2.97/1.01  --fof                                   false
% 2.97/1.01  --time_out_real                         305.
% 2.97/1.01  --time_out_virtual                      -1.
% 2.97/1.01  --symbol_type_check                     false
% 2.97/1.01  --clausify_out                          false
% 2.97/1.01  --sig_cnt_out                           false
% 2.97/1.01  --trig_cnt_out                          false
% 2.97/1.01  --trig_cnt_out_tolerance                1.
% 2.97/1.01  --trig_cnt_out_sk_spl                   false
% 2.97/1.01  --abstr_cl_out                          false
% 2.97/1.01  
% 2.97/1.01  ------ Global Options
% 2.97/1.01  
% 2.97/1.01  --schedule                              default
% 2.97/1.01  --add_important_lit                     false
% 2.97/1.01  --prop_solver_per_cl                    1000
% 2.97/1.01  --min_unsat_core                        false
% 2.97/1.01  --soft_assumptions                      false
% 2.97/1.01  --soft_lemma_size                       3
% 2.97/1.01  --prop_impl_unit_size                   0
% 2.97/1.01  --prop_impl_unit                        []
% 2.97/1.01  --share_sel_clauses                     true
% 2.97/1.01  --reset_solvers                         false
% 2.97/1.01  --bc_imp_inh                            [conj_cone]
% 2.97/1.01  --conj_cone_tolerance                   3.
% 2.97/1.01  --extra_neg_conj                        none
% 2.97/1.01  --large_theory_mode                     true
% 2.97/1.01  --prolific_symb_bound                   200
% 2.97/1.01  --lt_threshold                          2000
% 2.97/1.01  --clause_weak_htbl                      true
% 2.97/1.01  --gc_record_bc_elim                     false
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing Options
% 2.97/1.01  
% 2.97/1.01  --preprocessing_flag                    true
% 2.97/1.01  --time_out_prep_mult                    0.1
% 2.97/1.01  --splitting_mode                        input
% 2.97/1.01  --splitting_grd                         true
% 2.97/1.01  --splitting_cvd                         false
% 2.97/1.01  --splitting_cvd_svl                     false
% 2.97/1.01  --splitting_nvd                         32
% 2.97/1.01  --sub_typing                            true
% 2.97/1.01  --prep_gs_sim                           true
% 2.97/1.01  --prep_unflatten                        true
% 2.97/1.01  --prep_res_sim                          true
% 2.97/1.01  --prep_upred                            true
% 2.97/1.01  --prep_sem_filter                       exhaustive
% 2.97/1.01  --prep_sem_filter_out                   false
% 2.97/1.01  --pred_elim                             true
% 2.97/1.01  --res_sim_input                         true
% 2.97/1.01  --eq_ax_congr_red                       true
% 2.97/1.02  --pure_diseq_elim                       true
% 2.97/1.02  --brand_transform                       false
% 2.97/1.02  --non_eq_to_eq                          false
% 2.97/1.02  --prep_def_merge                        true
% 2.97/1.02  --prep_def_merge_prop_impl              false
% 2.97/1.02  --prep_def_merge_mbd                    true
% 2.97/1.02  --prep_def_merge_tr_red                 false
% 2.97/1.02  --prep_def_merge_tr_cl                  false
% 2.97/1.02  --smt_preprocessing                     true
% 2.97/1.02  --smt_ac_axioms                         fast
% 2.97/1.02  --preprocessed_out                      false
% 2.97/1.02  --preprocessed_stats                    false
% 2.97/1.02  
% 2.97/1.02  ------ Abstraction refinement Options
% 2.97/1.02  
% 2.97/1.02  --abstr_ref                             []
% 2.97/1.02  --abstr_ref_prep                        false
% 2.97/1.02  --abstr_ref_until_sat                   false
% 2.97/1.02  --abstr_ref_sig_restrict                funpre
% 2.97/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.02  --abstr_ref_under                       []
% 2.97/1.02  
% 2.97/1.02  ------ SAT Options
% 2.97/1.02  
% 2.97/1.02  --sat_mode                              false
% 2.97/1.02  --sat_fm_restart_options                ""
% 2.97/1.02  --sat_gr_def                            false
% 2.97/1.02  --sat_epr_types                         true
% 2.97/1.02  --sat_non_cyclic_types                  false
% 2.97/1.02  --sat_finite_models                     false
% 2.97/1.02  --sat_fm_lemmas                         false
% 2.97/1.02  --sat_fm_prep                           false
% 2.97/1.02  --sat_fm_uc_incr                        true
% 2.97/1.02  --sat_out_model                         small
% 2.97/1.02  --sat_out_clauses                       false
% 2.97/1.02  
% 2.97/1.02  ------ QBF Options
% 2.97/1.02  
% 2.97/1.02  --qbf_mode                              false
% 2.97/1.02  --qbf_elim_univ                         false
% 2.97/1.02  --qbf_dom_inst                          none
% 2.97/1.02  --qbf_dom_pre_inst                      false
% 2.97/1.02  --qbf_sk_in                             false
% 2.97/1.02  --qbf_pred_elim                         true
% 2.97/1.02  --qbf_split                             512
% 2.97/1.02  
% 2.97/1.02  ------ BMC1 Options
% 2.97/1.02  
% 2.97/1.02  --bmc1_incremental                      false
% 2.97/1.02  --bmc1_axioms                           reachable_all
% 2.97/1.02  --bmc1_min_bound                        0
% 2.97/1.02  --bmc1_max_bound                        -1
% 2.97/1.02  --bmc1_max_bound_default                -1
% 2.97/1.02  --bmc1_symbol_reachability              true
% 2.97/1.02  --bmc1_property_lemmas                  false
% 2.97/1.02  --bmc1_k_induction                      false
% 2.97/1.02  --bmc1_non_equiv_states                 false
% 2.97/1.02  --bmc1_deadlock                         false
% 2.97/1.02  --bmc1_ucm                              false
% 2.97/1.02  --bmc1_add_unsat_core                   none
% 2.97/1.02  --bmc1_unsat_core_children              false
% 2.97/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.02  --bmc1_out_stat                         full
% 2.97/1.02  --bmc1_ground_init                      false
% 2.97/1.02  --bmc1_pre_inst_next_state              false
% 2.97/1.02  --bmc1_pre_inst_state                   false
% 2.97/1.02  --bmc1_pre_inst_reach_state             false
% 2.97/1.02  --bmc1_out_unsat_core                   false
% 2.97/1.02  --bmc1_aig_witness_out                  false
% 2.97/1.02  --bmc1_verbose                          false
% 2.97/1.02  --bmc1_dump_clauses_tptp                false
% 2.97/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.02  --bmc1_dump_file                        -
% 2.97/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.02  --bmc1_ucm_extend_mode                  1
% 2.97/1.02  --bmc1_ucm_init_mode                    2
% 2.97/1.02  --bmc1_ucm_cone_mode                    none
% 2.97/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.02  --bmc1_ucm_relax_model                  4
% 2.97/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.02  --bmc1_ucm_layered_model                none
% 2.97/1.02  --bmc1_ucm_max_lemma_size               10
% 2.97/1.02  
% 2.97/1.02  ------ AIG Options
% 2.97/1.02  
% 2.97/1.02  --aig_mode                              false
% 2.97/1.02  
% 2.97/1.02  ------ Instantiation Options
% 2.97/1.02  
% 2.97/1.02  --instantiation_flag                    true
% 2.97/1.02  --inst_sos_flag                         false
% 2.97/1.02  --inst_sos_phase                        true
% 2.97/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.02  --inst_lit_sel_side                     none
% 2.97/1.02  --inst_solver_per_active                1400
% 2.97/1.02  --inst_solver_calls_frac                1.
% 2.97/1.02  --inst_passive_queue_type               priority_queues
% 2.97/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.02  --inst_passive_queues_freq              [25;2]
% 2.97/1.02  --inst_dismatching                      true
% 2.97/1.02  --inst_eager_unprocessed_to_passive     true
% 2.97/1.02  --inst_prop_sim_given                   true
% 2.97/1.02  --inst_prop_sim_new                     false
% 2.97/1.02  --inst_subs_new                         false
% 2.97/1.02  --inst_eq_res_simp                      false
% 2.97/1.02  --inst_subs_given                       false
% 2.97/1.02  --inst_orphan_elimination               true
% 2.97/1.02  --inst_learning_loop_flag               true
% 2.97/1.02  --inst_learning_start                   3000
% 2.97/1.02  --inst_learning_factor                  2
% 2.97/1.02  --inst_start_prop_sim_after_learn       3
% 2.97/1.02  --inst_sel_renew                        solver
% 2.97/1.02  --inst_lit_activity_flag                true
% 2.97/1.02  --inst_restr_to_given                   false
% 2.97/1.02  --inst_activity_threshold               500
% 2.97/1.02  --inst_out_proof                        true
% 2.97/1.02  
% 2.97/1.02  ------ Resolution Options
% 2.97/1.02  
% 2.97/1.02  --resolution_flag                       false
% 2.97/1.02  --res_lit_sel                           adaptive
% 2.97/1.02  --res_lit_sel_side                      none
% 2.97/1.02  --res_ordering                          kbo
% 2.97/1.02  --res_to_prop_solver                    active
% 2.97/1.02  --res_prop_simpl_new                    false
% 2.97/1.02  --res_prop_simpl_given                  true
% 2.97/1.02  --res_passive_queue_type                priority_queues
% 2.97/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.02  --res_passive_queues_freq               [15;5]
% 2.97/1.02  --res_forward_subs                      full
% 2.97/1.02  --res_backward_subs                     full
% 2.97/1.02  --res_forward_subs_resolution           true
% 2.97/1.02  --res_backward_subs_resolution          true
% 2.97/1.02  --res_orphan_elimination                true
% 2.97/1.02  --res_time_limit                        2.
% 2.97/1.02  --res_out_proof                         true
% 2.97/1.02  
% 2.97/1.02  ------ Superposition Options
% 2.97/1.02  
% 2.97/1.02  --superposition_flag                    true
% 2.97/1.02  --sup_passive_queue_type                priority_queues
% 2.97/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.02  --demod_completeness_check              fast
% 2.97/1.02  --demod_use_ground                      true
% 2.97/1.02  --sup_to_prop_solver                    passive
% 2.97/1.02  --sup_prop_simpl_new                    true
% 2.97/1.02  --sup_prop_simpl_given                  true
% 2.97/1.02  --sup_fun_splitting                     false
% 2.97/1.02  --sup_smt_interval                      50000
% 2.97/1.02  
% 2.97/1.02  ------ Superposition Simplification Setup
% 2.97/1.02  
% 2.97/1.02  --sup_indices_passive                   []
% 2.97/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.02  --sup_full_bw                           [BwDemod]
% 2.97/1.02  --sup_immed_triv                        [TrivRules]
% 2.97/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.02  --sup_immed_bw_main                     []
% 2.97/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.02  
% 2.97/1.02  ------ Combination Options
% 2.97/1.02  
% 2.97/1.02  --comb_res_mult                         3
% 2.97/1.02  --comb_sup_mult                         2
% 2.97/1.02  --comb_inst_mult                        10
% 2.97/1.02  
% 2.97/1.02  ------ Debug Options
% 2.97/1.02  
% 2.97/1.02  --dbg_backtrace                         false
% 2.97/1.02  --dbg_dump_prop_clauses                 false
% 2.97/1.02  --dbg_dump_prop_clauses_file            -
% 2.97/1.02  --dbg_out_stat                          false
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  ------ Proving...
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  % SZS status Theorem for theBenchmark.p
% 2.97/1.02  
% 2.97/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.02  
% 2.97/1.02  fof(f18,conjecture,(
% 2.97/1.02    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f19,negated_conjecture,(
% 2.97/1.02    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 2.97/1.02    inference(negated_conjecture,[],[f18])).
% 2.97/1.02  
% 2.97/1.02  fof(f23,plain,(
% 2.97/1.02    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 2.97/1.02    inference(ennf_transformation,[],[f19])).
% 2.97/1.02  
% 2.97/1.02  fof(f35,plain,(
% 2.97/1.02    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK3,sK4) = X0) )),
% 2.97/1.02    introduced(choice_axiom,[])).
% 2.97/1.02  
% 2.97/1.02  fof(f34,plain,(
% 2.97/1.02    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 2.97/1.02    introduced(choice_axiom,[])).
% 2.97/1.02  
% 2.97/1.02  fof(f36,plain,(
% 2.97/1.02    (k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & k4_tarski(sK3,sK4) = sK2),
% 2.97/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f35,f34])).
% 2.97/1.02  
% 2.97/1.02  fof(f77,plain,(
% 2.97/1.02    k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2),
% 2.97/1.02    inference(cnf_transformation,[],[f36])).
% 2.97/1.02  
% 2.97/1.02  fof(f76,plain,(
% 2.97/1.02    k4_tarski(sK3,sK4) = sK2),
% 2.97/1.02    inference(cnf_transformation,[],[f36])).
% 2.97/1.02  
% 2.97/1.02  fof(f17,axiom,(
% 2.97/1.02    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f74,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.97/1.02    inference(cnf_transformation,[],[f17])).
% 2.97/1.02  
% 2.97/1.02  fof(f75,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 2.97/1.02    inference(cnf_transformation,[],[f17])).
% 2.97/1.02  
% 2.97/1.02  fof(f14,axiom,(
% 2.97/1.02    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f53,plain,(
% 2.97/1.02    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.97/1.02    inference(cnf_transformation,[],[f14])).
% 2.97/1.02  
% 2.97/1.02  fof(f4,axiom,(
% 2.97/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f40,plain,(
% 2.97/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f4])).
% 2.97/1.02  
% 2.97/1.02  fof(f85,plain,(
% 2.97/1.02    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.97/1.02    inference(definition_unfolding,[],[f40,f82])).
% 2.97/1.02  
% 2.97/1.02  fof(f5,axiom,(
% 2.97/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f41,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f5])).
% 2.97/1.02  
% 2.97/1.02  fof(f6,axiom,(
% 2.97/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f42,plain,(
% 2.97/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f6])).
% 2.97/1.02  
% 2.97/1.02  fof(f7,axiom,(
% 2.97/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f43,plain,(
% 2.97/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f7])).
% 2.97/1.02  
% 2.97/1.02  fof(f8,axiom,(
% 2.97/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f44,plain,(
% 2.97/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f8])).
% 2.97/1.02  
% 2.97/1.02  fof(f9,axiom,(
% 2.97/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f45,plain,(
% 2.97/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f9])).
% 2.97/1.02  
% 2.97/1.02  fof(f10,axiom,(
% 2.97/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f46,plain,(
% 2.97/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f10])).
% 2.97/1.02  
% 2.97/1.02  fof(f78,plain,(
% 2.97/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.97/1.02    inference(definition_unfolding,[],[f45,f46])).
% 2.97/1.02  
% 2.97/1.02  fof(f79,plain,(
% 2.97/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.97/1.02    inference(definition_unfolding,[],[f44,f78])).
% 2.97/1.02  
% 2.97/1.02  fof(f80,plain,(
% 2.97/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.97/1.02    inference(definition_unfolding,[],[f43,f79])).
% 2.97/1.02  
% 2.97/1.02  fof(f81,plain,(
% 2.97/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.97/1.02    inference(definition_unfolding,[],[f42,f80])).
% 2.97/1.02  
% 2.97/1.02  fof(f82,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.97/1.02    inference(definition_unfolding,[],[f41,f81])).
% 2.97/1.02  
% 2.97/1.02  fof(f92,plain,(
% 2.97/1.02    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 2.97/1.02    inference(definition_unfolding,[],[f53,f82,f85,f82])).
% 2.97/1.02  
% 2.97/1.02  fof(f24,plain,(
% 2.97/1.02    ! [X6,X5,X4,X3,X2,X1,X0,X7] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 2.97/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.97/1.02  
% 2.97/1.02  fof(f28,plain,(
% 2.97/1.02    ! [X6,X5,X4,X3,X2,X1,X0,X7] : ((sP0(X6,X5,X4,X3,X2,X1,X0,X7) | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~r2_hidden(X8,X7))) | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)))),
% 2.97/1.02    inference(nnf_transformation,[],[f24])).
% 2.97/1.02  
% 2.97/1.02  fof(f29,plain,(
% 2.97/1.02    ! [X6,X5,X4,X3,X2,X1,X0,X7] : ((sP0(X6,X5,X4,X3,X2,X1,X0,X7) | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X7))) | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)))),
% 2.97/1.02    inference(flattening,[],[f28])).
% 2.97/1.02  
% 2.97/1.02  fof(f30,plain,(
% 2.97/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : (((X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8 & X6 != X8) | ~r2_hidden(X8,X7)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | X6 = X8 | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | ~r2_hidden(X9,X7))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 2.97/1.02    inference(rectify,[],[f29])).
% 2.97/1.02  
% 2.97/1.02  fof(f31,plain,(
% 2.97/1.02    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : (((X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8 & X6 != X8) | ~r2_hidden(X8,X7)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | X6 = X8 | r2_hidden(X8,X7))) => (((sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 2.97/1.02    introduced(choice_axiom,[])).
% 2.97/1.02  
% 2.97/1.02  fof(f32,plain,(
% 2.97/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | (((sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | ~r2_hidden(X9,X7))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 2.97/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 2.97/1.02  
% 2.97/1.02  fof(f56,plain,(
% 2.97/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | X6 != X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f32])).
% 2.97/1.02  
% 2.97/1.02  fof(f102,plain,(
% 2.97/1.02    ( ! [X4,X2,X0,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | ~sP0(X0,X1,X2,X3,X4,X5,X9,X7)) )),
% 2.97/1.02    inference(equality_resolution,[],[f56])).
% 2.97/1.02  
% 2.97/1.02  fof(f15,axiom,(
% 2.97/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f22,plain,(
% 2.97/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 2.97/1.02    inference(ennf_transformation,[],[f15])).
% 2.97/1.02  
% 2.97/1.02  fof(f25,plain,(
% 2.97/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> sP0(X6,X5,X4,X3,X2,X1,X0,X7))),
% 2.97/1.02    inference(definition_folding,[],[f22,f24])).
% 2.97/1.02  
% 2.97/1.02  fof(f33,plain,(
% 2.97/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)) & (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 2.97/1.02    inference(nnf_transformation,[],[f25])).
% 2.97/1.02  
% 2.97/1.02  fof(f71,plain,(
% 2.97/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 2.97/1.02    inference(cnf_transformation,[],[f33])).
% 2.97/1.02  
% 2.97/1.02  fof(f94,plain,(
% 2.97/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 2.97/1.02    inference(definition_unfolding,[],[f71,f46])).
% 2.97/1.02  
% 2.97/1.02  fof(f103,plain,(
% 2.97/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 2.97/1.02    inference(equality_resolution,[],[f94])).
% 2.97/1.02  
% 2.97/1.02  fof(f13,axiom,(
% 2.97/1.02    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f27,plain,(
% 2.97/1.02    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 2.97/1.02    inference(nnf_transformation,[],[f13])).
% 2.97/1.02  
% 2.97/1.02  fof(f51,plain,(
% 2.97/1.02    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f27])).
% 2.97/1.02  
% 2.97/1.02  fof(f2,axiom,(
% 2.97/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f38,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.97/1.02    inference(cnf_transformation,[],[f2])).
% 2.97/1.02  
% 2.97/1.02  fof(f16,axiom,(
% 2.97/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f73,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.97/1.02    inference(cnf_transformation,[],[f16])).
% 2.97/1.02  
% 2.97/1.02  fof(f83,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.97/1.02    inference(definition_unfolding,[],[f73,f82])).
% 2.97/1.02  
% 2.97/1.02  fof(f84,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.97/1.02    inference(definition_unfolding,[],[f38,f83])).
% 2.97/1.02  
% 2.97/1.02  fof(f90,plain,(
% 2.97/1.02    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.97/1.02    inference(definition_unfolding,[],[f51,f84,f85,f85,f85])).
% 2.97/1.02  
% 2.97/1.02  fof(f95,plain,(
% 2.97/1.02    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 2.97/1.02    inference(equality_resolution,[],[f90])).
% 2.97/1.02  
% 2.97/1.02  fof(f1,axiom,(
% 2.97/1.02    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f20,plain,(
% 2.97/1.02    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.97/1.02    inference(rectify,[],[f1])).
% 2.97/1.02  
% 2.97/1.02  fof(f37,plain,(
% 2.97/1.02    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.97/1.02    inference(cnf_transformation,[],[f20])).
% 2.97/1.02  
% 2.97/1.02  fof(f86,plain,(
% 2.97/1.02    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.97/1.02    inference(definition_unfolding,[],[f37,f83])).
% 2.97/1.02  
% 2.97/1.02  fof(f3,axiom,(
% 2.97/1.02    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f39,plain,(
% 2.97/1.02    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.97/1.02    inference(cnf_transformation,[],[f3])).
% 2.97/1.02  
% 2.97/1.02  fof(f11,axiom,(
% 2.97/1.02    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f26,plain,(
% 2.97/1.02    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.97/1.02    inference(nnf_transformation,[],[f11])).
% 2.97/1.02  
% 2.97/1.02  fof(f48,plain,(
% 2.97/1.02    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f26])).
% 2.97/1.02  
% 2.97/1.02  fof(f87,plain,(
% 2.97/1.02    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.97/1.02    inference(definition_unfolding,[],[f48,f85])).
% 2.97/1.02  
% 2.97/1.02  fof(f54,plain,(
% 2.97/1.02    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 2.97/1.02    inference(cnf_transformation,[],[f14])).
% 2.97/1.02  
% 2.97/1.02  fof(f91,plain,(
% 2.97/1.02    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 2.97/1.02    inference(definition_unfolding,[],[f54,f82,f82,f85])).
% 2.97/1.02  
% 2.97/1.02  fof(f12,axiom,(
% 2.97/1.02    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f21,plain,(
% 2.97/1.02    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 2.97/1.02    inference(ennf_transformation,[],[f12])).
% 2.97/1.02  
% 2.97/1.02  fof(f50,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 2.97/1.02    inference(cnf_transformation,[],[f21])).
% 2.97/1.02  
% 2.97/1.02  fof(f49,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 2.97/1.02    inference(cnf_transformation,[],[f21])).
% 2.97/1.02  
% 2.97/1.02  cnf(c_30,negated_conjecture,
% 2.97/1.02      ( k1_mcart_1(sK2) = sK2 | k2_mcart_1(sK2) = sK2 ),
% 2.97/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_31,negated_conjecture,
% 2.97/1.02      ( k4_tarski(sK3,sK4) = sK2 ),
% 2.97/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_29,plain,
% 2.97/1.02      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 2.97/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4183,plain,
% 2.97/1.02      ( k1_mcart_1(sK2) = sK3 ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_31,c_29]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4194,plain,
% 2.97/1.02      ( k2_mcart_1(sK2) = sK2 | sK3 = sK2 ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_30,c_4183]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_28,plain,
% 2.97/1.02      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 2.97/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4180,plain,
% 2.97/1.02      ( k2_mcart_1(sK2) = sK4 ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_31,c_28]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4196,plain,
% 2.97/1.02      ( sK4 = sK2 | sK3 = sK2 ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_4194,c_4180]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4199,plain,
% 2.97/1.02      ( k4_tarski(sK3,sK2) = sK2 | sK3 = sK2 ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_4196,c_31]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_9,plain,
% 2.97/1.02      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 2.97/1.02      inference(cnf_transformation,[],[f92]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4427,plain,
% 2.97/1.02      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0))
% 2.97/1.02      | sK3 = sK2 ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_4199,c_9]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_24,plain,
% 2.97/1.02      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) | r2_hidden(X6,X7) ),
% 2.97/1.02      inference(cnf_transformation,[],[f102]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_27,plain,
% 2.97/1.02      ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) ),
% 2.97/1.02      inference(cnf_transformation,[],[f103]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1585,plain,
% 2.97/1.02      ( r2_hidden(X0,X1)
% 2.97/1.02      | X2 != X3
% 2.97/1.02      | X4 != X0
% 2.97/1.02      | X5 != X6
% 2.97/1.02      | X7 != X8
% 2.97/1.02      | X9 != X10
% 2.97/1.02      | X11 != X12
% 2.97/1.02      | X13 != X14
% 2.97/1.02      | k6_enumset1(X4,X4,X5,X7,X9,X11,X13,X2) != X1 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_27]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1586,plain,
% 2.97/1.02      ( r2_hidden(X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_1585]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1587,plain,
% 2.97/1.02      ( r2_hidden(X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) = iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_1586]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1589,plain,
% 2.97/1.02      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_1587]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_7,plain,
% 2.97/1.02      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f95]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_0,plain,
% 2.97/1.02      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 2.97/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1,plain,
% 2.97/1.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.97/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4102,plain,
% 2.97/1.02      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_7,c_0,c_1]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4131,plain,
% 2.97/1.02      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_4102]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2,plain,
% 2.97/1.02      ( ~ r2_hidden(X0,X1)
% 2.97/1.02      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 2.97/1.02      inference(cnf_transformation,[],[f87]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4306,plain,
% 2.97/1.02      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))
% 2.97/1.02      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4310,plain,
% 2.97/1.02      ( r2_hidden(X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) != iProver_top
% 2.97/1.02      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) = iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_4306]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4312,plain,
% 2.97/1.02      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 2.97/1.02      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_4310]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_8,plain,
% 2.97/1.02      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 2.97/1.02      inference(cnf_transformation,[],[f91]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4391,plain,
% 2.97/1.02      ( k6_enumset1(k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),sK2) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_31,c_8]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4642,plain,
% 2.97/1.02      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_31,c_4391]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4786,plain,
% 2.97/1.02      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 2.97/1.02      | sK3 = sK2 ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_4196,c_4642]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4,plain,
% 2.97/1.02      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 2.97/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3971,plain,
% 2.97/1.02      ( k1_xboole_0 = X0
% 2.97/1.02      | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_5179,plain,
% 2.97/1.02      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 2.97/1.02      | sK3 = sK2
% 2.97/1.02      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_4786,c_3971]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_6111,plain,
% 2.97/1.02      ( sK3 = sK2 ),
% 2.97/1.02      inference(global_propositional_subsumption,
% 2.97/1.02                [status(thm)],
% 2.97/1.02                [c_4427,c_1589,c_4131,c_4312,c_5179]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_5,plain,
% 2.97/1.02      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 2.97/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3970,plain,
% 2.97/1.02      ( k1_xboole_0 = X0
% 2.97/1.02      | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_5144,plain,
% 2.97/1.02      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 2.97/1.02      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_4642,c_3970]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_5600,plain,
% 2.97/1.02      ( r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 2.97/1.02      inference(forward_subsumption_resolution,
% 2.97/1.02                [status(thm)],
% 2.97/1.02                [c_5144,c_4102]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_6117,plain,
% 2.97/1.02      ( r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_6111,c_5600]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(contradiction,plain,
% 2.97/1.02      ( $false ),
% 2.97/1.02      inference(minisat,[status(thm)],[c_6117,c_4312,c_1589]) ).
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.02  
% 2.97/1.02  ------                               Statistics
% 2.97/1.02  
% 2.97/1.02  ------ General
% 2.97/1.02  
% 2.97/1.02  abstr_ref_over_cycles:                  0
% 2.97/1.02  abstr_ref_under_cycles:                 0
% 2.97/1.02  gc_basic_clause_elim:                   0
% 2.97/1.02  forced_gc_time:                         0
% 2.97/1.02  parsing_time:                           0.012
% 2.97/1.02  unif_index_cands_time:                  0.
% 2.97/1.02  unif_index_add_time:                    0.
% 2.97/1.02  orderings_time:                         0.
% 2.97/1.02  out_proof_time:                         0.009
% 2.97/1.02  total_time:                             0.245
% 2.97/1.02  num_of_symbols:                         46
% 2.97/1.02  num_of_terms:                           6456
% 2.97/1.02  
% 2.97/1.02  ------ Preprocessing
% 2.97/1.02  
% 2.97/1.02  num_of_splits:                          0
% 2.97/1.02  num_of_split_atoms:                     0
% 2.97/1.02  num_of_reused_defs:                     0
% 2.97/1.02  num_eq_ax_congr_red:                    32
% 2.97/1.02  num_of_sem_filtered_clauses:            1
% 2.97/1.02  num_of_subtypes:                        0
% 2.97/1.02  monotx_restored_types:                  0
% 2.97/1.02  sat_num_of_epr_types:                   0
% 2.97/1.02  sat_num_of_non_cyclic_types:            0
% 2.97/1.02  sat_guarded_non_collapsed_types:        0
% 2.97/1.02  num_pure_diseq_elim:                    0
% 2.97/1.02  simp_replaced_by:                       0
% 2.97/1.02  res_preprocessed:                       121
% 2.97/1.02  prep_upred:                             0
% 2.97/1.02  prep_unflattend:                        222
% 2.97/1.02  smt_new_axioms:                         0
% 2.97/1.02  pred_elim_cands:                        3
% 2.97/1.02  pred_elim:                              0
% 2.97/1.02  pred_elim_cl:                           0
% 2.97/1.02  pred_elim_cycles:                       3
% 2.97/1.02  merged_defs:                            6
% 2.97/1.02  merged_defs_ncl:                        0
% 2.97/1.02  bin_hyper_res:                          6
% 2.97/1.02  prep_cycles:                            3
% 2.97/1.02  pred_elim_time:                         0.05
% 2.97/1.02  splitting_time:                         0.
% 2.97/1.02  sem_filter_time:                        0.
% 2.97/1.02  monotx_time:                            0.001
% 2.97/1.02  subtype_inf_time:                       0.
% 2.97/1.02  
% 2.97/1.02  ------ Problem properties
% 2.97/1.02  
% 2.97/1.02  clauses:                                32
% 2.97/1.02  conjectures:                            2
% 2.97/1.02  epr:                                    8
% 2.97/1.02  horn:                                   28
% 2.97/1.02  ground:                                 2
% 2.97/1.02  unary:                                  9
% 2.97/1.02  binary:                                 14
% 2.97/1.02  lits:                                   76
% 2.97/1.02  lits_eq:                                36
% 2.97/1.02  fd_pure:                                0
% 2.97/1.02  fd_pseudo:                              0
% 2.97/1.02  fd_cond:                                2
% 2.97/1.02  fd_pseudo_cond:                         3
% 2.97/1.02  ac_symbols:                             0
% 2.97/1.02  
% 2.97/1.02  ------ Propositional Solver
% 2.97/1.02  
% 2.97/1.02  prop_solver_calls:                      23
% 2.97/1.02  prop_fast_solver_calls:                 1290
% 2.97/1.02  smt_solver_calls:                       0
% 2.97/1.02  smt_fast_solver_calls:                  0
% 2.97/1.02  prop_num_of_clauses:                    1400
% 2.97/1.02  prop_preprocess_simplified:             6325
% 2.97/1.02  prop_fo_subsumed:                       1
% 2.97/1.02  prop_solver_time:                       0.
% 2.97/1.02  smt_solver_time:                        0.
% 2.97/1.02  smt_fast_solver_time:                   0.
% 2.97/1.02  prop_fast_solver_time:                  0.
% 2.97/1.02  prop_unsat_core_time:                   0.
% 2.97/1.02  
% 2.97/1.02  ------ QBF
% 2.97/1.02  
% 2.97/1.02  qbf_q_res:                              0
% 2.97/1.02  qbf_num_tautologies:                    0
% 2.97/1.02  qbf_prep_cycles:                        0
% 2.97/1.02  
% 2.97/1.02  ------ BMC1
% 2.97/1.02  
% 2.97/1.02  bmc1_current_bound:                     -1
% 2.97/1.02  bmc1_last_solved_bound:                 -1
% 2.97/1.02  bmc1_unsat_core_size:                   -1
% 2.97/1.02  bmc1_unsat_core_parents_size:           -1
% 2.97/1.02  bmc1_merge_next_fun:                    0
% 2.97/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.02  
% 2.97/1.02  ------ Instantiation
% 2.97/1.02  
% 2.97/1.02  inst_num_of_clauses:                    394
% 2.97/1.02  inst_num_in_passive:                    253
% 2.97/1.02  inst_num_in_active:                     124
% 2.97/1.02  inst_num_in_unprocessed:                17
% 2.97/1.02  inst_num_of_loops:                      170
% 2.97/1.02  inst_num_of_learning_restarts:          0
% 2.97/1.02  inst_num_moves_active_passive:          44
% 2.97/1.02  inst_lit_activity:                      0
% 2.97/1.02  inst_lit_activity_moves:                0
% 2.97/1.02  inst_num_tautologies:                   0
% 2.97/1.02  inst_num_prop_implied:                  0
% 2.97/1.02  inst_num_existing_simplified:           0
% 2.97/1.02  inst_num_eq_res_simplified:             0
% 2.97/1.02  inst_num_child_elim:                    0
% 2.97/1.02  inst_num_of_dismatching_blockings:      75
% 2.97/1.02  inst_num_of_non_proper_insts:           337
% 2.97/1.02  inst_num_of_duplicates:                 0
% 2.97/1.02  inst_inst_num_from_inst_to_res:         0
% 2.97/1.02  inst_dismatching_checking_time:         0.
% 2.97/1.02  
% 2.97/1.02  ------ Resolution
% 2.97/1.02  
% 2.97/1.02  res_num_of_clauses:                     0
% 2.97/1.02  res_num_in_passive:                     0
% 2.97/1.02  res_num_in_active:                      0
% 2.97/1.02  res_num_of_loops:                       124
% 2.97/1.02  res_forward_subset_subsumed:            12
% 2.97/1.02  res_backward_subset_subsumed:           0
% 2.97/1.02  res_forward_subsumed:                   0
% 2.97/1.02  res_backward_subsumed:                  0
% 2.97/1.02  res_forward_subsumption_resolution:     0
% 2.97/1.02  res_backward_subsumption_resolution:    0
% 2.97/1.02  res_clause_to_clause_subsumption:       2792
% 2.97/1.02  res_orphan_elimination:                 0
% 2.97/1.02  res_tautology_del:                      38
% 2.97/1.02  res_num_eq_res_simplified:              0
% 2.97/1.02  res_num_sel_changes:                    0
% 2.97/1.02  res_moves_from_active_to_pass:          0
% 2.97/1.02  
% 2.97/1.02  ------ Superposition
% 2.97/1.02  
% 2.97/1.02  sup_time_total:                         0.
% 2.97/1.02  sup_time_generating:                    0.
% 2.97/1.02  sup_time_sim_full:                      0.
% 2.97/1.02  sup_time_sim_immed:                     0.
% 2.97/1.02  
% 2.97/1.02  sup_num_of_clauses:                     55
% 2.97/1.02  sup_num_in_active:                      16
% 2.97/1.02  sup_num_in_passive:                     39
% 2.97/1.02  sup_num_of_loops:                       32
% 2.97/1.02  sup_fw_superposition:                   162
% 2.97/1.02  sup_bw_superposition:                   10
% 2.97/1.02  sup_immediate_simplified:               6
% 2.97/1.02  sup_given_eliminated:                   0
% 2.97/1.02  comparisons_done:                       0
% 2.97/1.02  comparisons_avoided:                    14
% 2.97/1.02  
% 2.97/1.02  ------ Simplifications
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  sim_fw_subset_subsumed:                 2
% 2.97/1.02  sim_bw_subset_subsumed:                 2
% 2.97/1.02  sim_fw_subsumed:                        1
% 2.97/1.02  sim_bw_subsumed:                        0
% 2.97/1.02  sim_fw_subsumption_res:                 4
% 2.97/1.02  sim_bw_subsumption_res:                 0
% 2.97/1.02  sim_tautology_del:                      0
% 2.97/1.02  sim_eq_tautology_del:                   7
% 2.97/1.02  sim_eq_res_simp:                        0
% 2.97/1.02  sim_fw_demodulated:                     3
% 2.97/1.02  sim_bw_demodulated:                     16
% 2.97/1.02  sim_light_normalised:                   1
% 2.97/1.02  sim_joinable_taut:                      0
% 2.97/1.02  sim_joinable_simp:                      0
% 2.97/1.02  sim_ac_normalised:                      0
% 2.97/1.02  sim_smt_subsumption:                    0
% 2.97/1.02  
%------------------------------------------------------------------------------
