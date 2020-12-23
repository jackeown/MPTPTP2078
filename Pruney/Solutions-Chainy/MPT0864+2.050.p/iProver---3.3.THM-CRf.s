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
% DateTime   : Thu Dec  3 11:57:55 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 893 expanded)
%              Number of clauses        :   50 (  89 expanded)
%              Number of leaves         :   24 ( 281 expanded)
%              Depth                    :   17
%              Number of atoms          :  351 (1474 expanded)
%              Number of equality atoms :  277 (1313 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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

fof(f26,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK3,sK4) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK2) = sK2
        | k1_mcart_1(sK2) = sK2 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK2 ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( k2_mcart_1(sK2) = sK2
      | k1_mcart_1(sK2) = sK2 )
    & k4_tarski(sK3,sK4) = sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f38,f37])).

fof(f78,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f83])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f87])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f96,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f58,f83,f87,f83])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f32,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5) != X0
            & sK1(X0,X1,X2,X3,X4,X5) != X1
            & sK1(X0,X1,X2,X3,X4,X5) != X2
            & sK1(X0,X1,X2,X3,X4,X5) != X3
            & sK1(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK1(X0,X1,X2,X3,X4,X5) = X0
          | sK1(X0,X1,X2,X3,X4,X5) = X1
          | sK1(X0,X1,X2,X3,X4,X5) = X2
          | sK1(X0,X1,X2,X3,X4,X5) = X3
          | sK1(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5) != X0
              & sK1(X0,X1,X2,X3,X4,X5) != X1
              & sK1(X0,X1,X2,X3,X4,X5) != X2
              & sK1(X0,X1,X2,X3,X4,X5) != X3
              & sK1(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK1(X0,X1,X2,X3,X4,X5) = X0
            | sK1(X0,X1,X2,X3,X4,X5) = X1
            | sK1(X0,X1,X2,X3,X4,X5) = X2
            | sK1(X0,X1,X2,X3,X4,X5) = X3
            | sK1(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f61,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X7,X5) ) ),
    inference(equality_resolution,[],[f61])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f25,f27])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f72,f80])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f98])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f59,f83,f83,f87])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f83])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f85])).

fof(f94,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f56,f86,f87,f87,f87])).

fof(f99,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f94])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f85])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f88,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f84])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f43,f86,f84])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_27,negated_conjecture,
    ( k1_mcart_1(sK2) = sK2
    | k2_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_26,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2813,plain,
    ( k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_28,c_26])).

cnf(c_2815,plain,
    ( k2_mcart_1(sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_27,c_2813])).

cnf(c_25,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2796,plain,
    ( k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_28,c_25])).

cnf(c_2817,plain,
    ( sK4 = sK2
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_2815,c_2796])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2606,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4499,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_28,c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2604,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6316,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4499,c_2604])).

cnf(c_10820,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2606,c_6316])).

cnf(c_10823,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10820,c_28])).

cnf(c_11143,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | sK3 = sK2
    | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2817,c_10823])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X4,X5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_24,plain,
    ( sP0(X0,X1,X2,X3,X4,k6_enumset1(X4,X4,X4,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1021,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | k6_enumset1(X4,X4,X4,X4,X5,X7,X9,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_24])).

cnf(c_1022,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
    inference(unflattening,[status(thm)],[c_1021])).

cnf(c_1024,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_2958,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2963,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2958])).

cnf(c_9,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3330,plain,
    ( k6_enumset1(k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),sK2) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_28,c_9])).

cnf(c_3539,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_28,c_3330])).

cnf(c_3560,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_2817,c_3539])).

cnf(c_6315,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK3 = sK2
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3560,c_2604])).

cnf(c_6348,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK3 = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6315])).

cnf(c_8,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2727,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_8,c_1])).

cnf(c_0,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3127,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_3128,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3127,c_1])).

cnf(c_11448,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2727,c_3128])).

cnf(c_11450,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11448])).

cnf(c_11455,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11143,c_1024,c_2963,c_6348,c_11450])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2603,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4800,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3539,c_2603])).

cnf(c_11476,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11455,c_4800])).

cnf(c_2962,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2958])).

cnf(c_2964,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2962])).

cnf(c_1023,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_1025,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11476,c_11450,c_2964,c_1025])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.01/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/0.99  
% 4.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/0.99  
% 4.01/0.99  ------  iProver source info
% 4.01/0.99  
% 4.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/0.99  git: non_committed_changes: false
% 4.01/0.99  git: last_make_outside_of_git: false
% 4.01/0.99  
% 4.01/0.99  ------ 
% 4.01/0.99  ------ Parsing...
% 4.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/0.99  
% 4.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.01/0.99  
% 4.01/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/0.99  
% 4.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/0.99  ------ Proving...
% 4.01/0.99  ------ Problem Properties 
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  clauses                                 29
% 4.01/0.99  conjectures                             2
% 4.01/0.99  EPR                                     6
% 4.01/0.99  Horn                                    25
% 4.01/0.99  unary                                   10
% 4.01/0.99  binary                                  12
% 4.01/0.99  lits                                    63
% 4.01/0.99  lits eq                                 31
% 4.01/0.99  fd_pure                                 0
% 4.01/0.99  fd_pseudo                               0
% 4.01/0.99  fd_cond                                 2
% 4.01/0.99  fd_pseudo_cond                          3
% 4.01/0.99  AC symbols                              0
% 4.01/0.99  
% 4.01/0.99  ------ Input Options Time Limit: Unbounded
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  ------ 
% 4.01/0.99  Current options:
% 4.01/0.99  ------ 
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  ------ Proving...
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  % SZS status Theorem for theBenchmark.p
% 4.01/0.99  
% 4.01/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/0.99  
% 4.01/0.99  fof(f20,conjecture,(
% 4.01/0.99    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f21,negated_conjecture,(
% 4.01/0.99    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 4.01/0.99    inference(negated_conjecture,[],[f20])).
% 4.01/0.99  
% 4.01/0.99  fof(f26,plain,(
% 4.01/0.99    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 4.01/0.99    inference(ennf_transformation,[],[f21])).
% 4.01/0.99  
% 4.01/0.99  fof(f38,plain,(
% 4.01/0.99    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK3,sK4) = X0) )),
% 4.01/0.99    introduced(choice_axiom,[])).
% 4.01/0.99  
% 4.01/0.99  fof(f37,plain,(
% 4.01/0.99    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 4.01/0.99    introduced(choice_axiom,[])).
% 4.01/0.99  
% 4.01/0.99  fof(f39,plain,(
% 4.01/0.99    (k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & k4_tarski(sK3,sK4) = sK2),
% 4.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f38,f37])).
% 4.01/0.99  
% 4.01/0.99  fof(f78,plain,(
% 4.01/0.99    k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2),
% 4.01/0.99    inference(cnf_transformation,[],[f39])).
% 4.01/0.99  
% 4.01/0.99  fof(f77,plain,(
% 4.01/0.99    k4_tarski(sK3,sK4) = sK2),
% 4.01/0.99    inference(cnf_transformation,[],[f39])).
% 4.01/0.99  
% 4.01/0.99  fof(f19,axiom,(
% 4.01/0.99    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f75,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 4.01/0.99    inference(cnf_transformation,[],[f19])).
% 4.01/0.99  
% 4.01/0.99  fof(f76,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 4.01/0.99    inference(cnf_transformation,[],[f19])).
% 4.01/0.99  
% 4.01/0.99  fof(f12,axiom,(
% 4.01/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f29,plain,(
% 4.01/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 4.01/0.99    inference(nnf_transformation,[],[f12])).
% 4.01/0.99  
% 4.01/0.99  fof(f52,plain,(
% 4.01/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f29])).
% 4.01/0.99  
% 4.01/0.99  fof(f5,axiom,(
% 4.01/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f44,plain,(
% 4.01/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f5])).
% 4.01/0.99  
% 4.01/0.99  fof(f6,axiom,(
% 4.01/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f45,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f6])).
% 4.01/0.99  
% 4.01/0.99  fof(f7,axiom,(
% 4.01/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f46,plain,(
% 4.01/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f7])).
% 4.01/0.99  
% 4.01/0.99  fof(f8,axiom,(
% 4.01/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f47,plain,(
% 4.01/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f8])).
% 4.01/0.99  
% 4.01/0.99  fof(f9,axiom,(
% 4.01/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f48,plain,(
% 4.01/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f9])).
% 4.01/0.99  
% 4.01/0.99  fof(f10,axiom,(
% 4.01/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f49,plain,(
% 4.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f10])).
% 4.01/0.99  
% 4.01/0.99  fof(f11,axiom,(
% 4.01/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f50,plain,(
% 4.01/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f11])).
% 4.01/0.99  
% 4.01/0.99  fof(f79,plain,(
% 4.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f49,f50])).
% 4.01/0.99  
% 4.01/0.99  fof(f80,plain,(
% 4.01/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f48,f79])).
% 4.01/0.99  
% 4.01/0.99  fof(f81,plain,(
% 4.01/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f47,f80])).
% 4.01/0.99  
% 4.01/0.99  fof(f82,plain,(
% 4.01/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f46,f81])).
% 4.01/0.99  
% 4.01/0.99  fof(f83,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f45,f82])).
% 4.01/0.99  
% 4.01/0.99  fof(f87,plain,(
% 4.01/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f44,f83])).
% 4.01/0.99  
% 4.01/0.99  fof(f91,plain,(
% 4.01/0.99    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f52,f87])).
% 4.01/0.99  
% 4.01/0.99  fof(f16,axiom,(
% 4.01/0.99    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f58,plain,(
% 4.01/0.99    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 4.01/0.99    inference(cnf_transformation,[],[f16])).
% 4.01/0.99  
% 4.01/0.99  fof(f96,plain,(
% 4.01/0.99    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 4.01/0.99    inference(definition_unfolding,[],[f58,f83,f87,f83])).
% 4.01/0.99  
% 4.01/0.99  fof(f14,axiom,(
% 4.01/0.99    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f24,plain,(
% 4.01/0.99    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 4.01/0.99    inference(ennf_transformation,[],[f14])).
% 4.01/0.99  
% 4.01/0.99  fof(f55,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 4.01/0.99    inference(cnf_transformation,[],[f24])).
% 4.01/0.99  
% 4.01/0.99  fof(f27,plain,(
% 4.01/0.99    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 4.01/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.01/0.99  
% 4.01/0.99  fof(f31,plain,(
% 4.01/0.99    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 4.01/0.99    inference(nnf_transformation,[],[f27])).
% 4.01/0.99  
% 4.01/0.99  fof(f32,plain,(
% 4.01/0.99    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 4.01/0.99    inference(flattening,[],[f31])).
% 4.01/0.99  
% 4.01/0.99  fof(f33,plain,(
% 4.01/0.99    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 4.01/0.99    inference(rectify,[],[f32])).
% 4.01/0.99  
% 4.01/0.99  fof(f34,plain,(
% 4.01/0.99    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5))))),
% 4.01/0.99    introduced(choice_axiom,[])).
% 4.01/0.99  
% 4.01/0.99  fof(f35,plain,(
% 4.01/0.99    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK1(X0,X1,X2,X3,X4,X5) != X0 & sK1(X0,X1,X2,X3,X4,X5) != X1 & sK1(X0,X1,X2,X3,X4,X5) != X2 & sK1(X0,X1,X2,X3,X4,X5) != X3 & sK1(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)) & (sK1(X0,X1,X2,X3,X4,X5) = X0 | sK1(X0,X1,X2,X3,X4,X5) = X1 | sK1(X0,X1,X2,X3,X4,X5) = X2 | sK1(X0,X1,X2,X3,X4,X5) = X3 | sK1(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 4.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 4.01/0.99  
% 4.01/0.99  fof(f61,plain,(
% 4.01/0.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f35])).
% 4.01/0.99  
% 4.01/0.99  fof(f104,plain,(
% 4.01/0.99    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X7,X5)) )),
% 4.01/0.99    inference(equality_resolution,[],[f61])).
% 4.01/0.99  
% 4.01/0.99  fof(f17,axiom,(
% 4.01/0.99    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f25,plain,(
% 4.01/0.99    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 4.01/0.99    inference(ennf_transformation,[],[f17])).
% 4.01/0.99  
% 4.01/0.99  fof(f28,plain,(
% 4.01/0.99    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 4.01/0.99    inference(definition_folding,[],[f25,f27])).
% 4.01/0.99  
% 4.01/0.99  fof(f36,plain,(
% 4.01/0.99    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 4.01/0.99    inference(nnf_transformation,[],[f28])).
% 4.01/0.99  
% 4.01/0.99  fof(f72,plain,(
% 4.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 4.01/0.99    inference(cnf_transformation,[],[f36])).
% 4.01/0.99  
% 4.01/0.99  fof(f98,plain,(
% 4.01/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 4.01/0.99    inference(definition_unfolding,[],[f72,f80])).
% 4.01/0.99  
% 4.01/0.99  fof(f105,plain,(
% 4.01/0.99    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))) )),
% 4.01/0.99    inference(equality_resolution,[],[f98])).
% 4.01/0.99  
% 4.01/0.99  fof(f59,plain,(
% 4.01/0.99    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 4.01/0.99    inference(cnf_transformation,[],[f16])).
% 4.01/0.99  
% 4.01/0.99  fof(f95,plain,(
% 4.01/0.99    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 4.01/0.99    inference(definition_unfolding,[],[f59,f83,f83,f87])).
% 4.01/0.99  
% 4.01/0.99  fof(f15,axiom,(
% 4.01/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f30,plain,(
% 4.01/0.99    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 4.01/0.99    inference(nnf_transformation,[],[f15])).
% 4.01/0.99  
% 4.01/0.99  fof(f56,plain,(
% 4.01/0.99    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f30])).
% 4.01/0.99  
% 4.01/0.99  fof(f3,axiom,(
% 4.01/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f42,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.01/0.99    inference(cnf_transformation,[],[f3])).
% 4.01/0.99  
% 4.01/0.99  fof(f18,axiom,(
% 4.01/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f74,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.01/0.99    inference(cnf_transformation,[],[f18])).
% 4.01/0.99  
% 4.01/0.99  fof(f85,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.01/0.99    inference(definition_unfolding,[],[f74,f83])).
% 4.01/0.99  
% 4.01/0.99  fof(f86,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.01/0.99    inference(definition_unfolding,[],[f42,f85])).
% 4.01/0.99  
% 4.01/0.99  fof(f94,plain,(
% 4.01/0.99    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f56,f86,f87,f87,f87])).
% 4.01/0.99  
% 4.01/0.99  fof(f99,plain,(
% 4.01/0.99    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 4.01/0.99    inference(equality_resolution,[],[f94])).
% 4.01/0.99  
% 4.01/0.99  fof(f2,axiom,(
% 4.01/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f23,plain,(
% 4.01/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.01/0.99    inference(rectify,[],[f2])).
% 4.01/0.99  
% 4.01/0.99  fof(f41,plain,(
% 4.01/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.01/0.99    inference(cnf_transformation,[],[f23])).
% 4.01/0.99  
% 4.01/0.99  fof(f89,plain,(
% 4.01/0.99    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 4.01/0.99    inference(definition_unfolding,[],[f41,f85])).
% 4.01/0.99  
% 4.01/0.99  fof(f1,axiom,(
% 4.01/0.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f22,plain,(
% 4.01/0.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.01/0.99    inference(rectify,[],[f1])).
% 4.01/0.99  
% 4.01/0.99  fof(f40,plain,(
% 4.01/0.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.01/0.99    inference(cnf_transformation,[],[f22])).
% 4.01/0.99  
% 4.01/0.99  fof(f13,axiom,(
% 4.01/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f53,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.01/0.99    inference(cnf_transformation,[],[f13])).
% 4.01/0.99  
% 4.01/0.99  fof(f84,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.01/0.99    inference(definition_unfolding,[],[f53,f83])).
% 4.01/0.99  
% 4.01/0.99  fof(f88,plain,(
% 4.01/0.99    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 4.01/0.99    inference(definition_unfolding,[],[f40,f84])).
% 4.01/0.99  
% 4.01/0.99  fof(f4,axiom,(
% 4.01/0.99    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 4.01/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f43,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 4.01/0.99    inference(cnf_transformation,[],[f4])).
% 4.01/0.99  
% 4.01/0.99  fof(f90,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0) )),
% 4.01/0.99    inference(definition_unfolding,[],[f43,f86,f84])).
% 4.01/0.99  
% 4.01/0.99  fof(f54,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 4.01/0.99    inference(cnf_transformation,[],[f24])).
% 4.01/0.99  
% 4.01/0.99  cnf(c_27,negated_conjecture,
% 4.01/0.99      ( k1_mcart_1(sK2) = sK2 | k2_mcart_1(sK2) = sK2 ),
% 4.01/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_28,negated_conjecture,
% 4.01/0.99      ( k4_tarski(sK3,sK4) = sK2 ),
% 4.01/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_26,plain,
% 4.01/0.99      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2813,plain,
% 4.01/0.99      ( k1_mcart_1(sK2) = sK3 ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_28,c_26]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2815,plain,
% 4.01/0.99      ( k2_mcart_1(sK2) = sK2 | sK3 = sK2 ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_27,c_2813]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_25,plain,
% 4.01/0.99      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 4.01/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2796,plain,
% 4.01/0.99      ( k2_mcart_1(sK2) = sK4 ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_28,c_25]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2817,plain,
% 4.01/0.99      ( sK4 = sK2 | sK3 = sK2 ),
% 4.01/0.99      inference(demodulation,[status(thm)],[c_2815,c_2796]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_3,plain,
% 4.01/0.99      ( ~ r2_hidden(X0,X1)
% 4.01/0.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 4.01/0.99      inference(cnf_transformation,[],[f91]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2606,plain,
% 4.01/0.99      ( r2_hidden(X0,X1) != iProver_top
% 4.01/0.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_10,plain,
% 4.01/0.99      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 4.01/0.99      inference(cnf_transformation,[],[f96]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_4499,plain,
% 4.01/0.99      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0)) ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_28,c_10]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_5,plain,
% 4.01/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f55]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2604,plain,
% 4.01/0.99      ( k1_xboole_0 = X0
% 4.01/0.99      | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_6316,plain,
% 4.01/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0) = k1_xboole_0
% 4.01/0.99      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0))) != iProver_top ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_4499,c_2604]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_10820,plain,
% 4.01/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 4.01/0.99      | r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,sK4))) != iProver_top ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_2606,c_6316]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_10823,plain,
% 4.01/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 4.01/0.99      | r2_hidden(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 4.01/0.99      inference(light_normalisation,[status(thm)],[c_10820,c_28]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_11143,plain,
% 4.01/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 4.01/0.99      | sK3 = sK2
% 4.01/0.99      | r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_2817,c_10823]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_21,plain,
% 4.01/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X4,X5) ),
% 4.01/0.99      inference(cnf_transformation,[],[f104]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_24,plain,
% 4.01/0.99      ( sP0(X0,X1,X2,X3,X4,k6_enumset1(X4,X4,X4,X4,X3,X2,X1,X0)) ),
% 4.01/0.99      inference(cnf_transformation,[],[f105]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1021,plain,
% 4.01/0.99      ( r2_hidden(X0,X1)
% 4.01/0.99      | X2 != X3
% 4.01/0.99      | X4 != X0
% 4.01/0.99      | X5 != X6
% 4.01/0.99      | X7 != X8
% 4.01/0.99      | X9 != X10
% 4.01/0.99      | k6_enumset1(X4,X4,X4,X4,X5,X7,X9,X2) != X1 ),
% 4.01/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_24]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1022,plain,
% 4.01/0.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
% 4.01/0.99      inference(unflattening,[status(thm)],[c_1021]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1024,plain,
% 4.01/0.99      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_1022]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2958,plain,
% 4.01/0.99      ( ~ r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4))
% 4.01/0.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2963,plain,
% 4.01/0.99      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 4.01/0.99      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_2958]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_9,plain,
% 4.01/0.99      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 4.01/0.99      inference(cnf_transformation,[],[f95]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_3330,plain,
% 4.01/0.99      ( k6_enumset1(k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),sK2) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_28,c_9]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_3539,plain,
% 4.01/0.99      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_28,c_3330]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_3560,plain,
% 4.01/0.99      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 4.01/0.99      | sK3 = sK2 ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_2817,c_3539]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_6315,plain,
% 4.01/0.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 4.01/0.99      | sK3 = sK2
% 4.01/0.99      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_3560,c_2604]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_6348,plain,
% 4.01/0.99      ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 4.01/0.99      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 4.01/0.99      | sK3 = sK2 ),
% 4.01/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6315]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_8,plain,
% 4.01/0.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 4.01/0.99      inference(cnf_transformation,[],[f99]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1,plain,
% 4.01/0.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f89]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2727,plain,
% 4.01/0.99      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 4.01/0.99      inference(demodulation,[status(thm)],[c_8,c_1]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_0,plain,
% 4.01/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f88]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2,plain,
% 4.01/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f90]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_3127,plain,
% 4.01/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_3128,plain,
% 4.01/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.01/0.99      inference(light_normalisation,[status(thm)],[c_3127,c_1]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_11448,plain,
% 4.01/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 4.01/0.99      inference(demodulation,[status(thm)],[c_2727,c_3128]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_11450,plain,
% 4.01/0.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_11448]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_11455,plain,
% 4.01/0.99      ( sK3 = sK2 ),
% 4.01/0.99      inference(global_propositional_subsumption,
% 4.01/0.99                [status(thm)],
% 4.01/0.99                [c_11143,c_1024,c_2963,c_6348,c_11450]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_6,plain,
% 4.01/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2603,plain,
% 4.01/0.99      ( k1_xboole_0 = X0
% 4.01/0.99      | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_4800,plain,
% 4.01/0.99      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 4.01/0.99      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_3539,c_2603]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_11476,plain,
% 4.01/0.99      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 4.01/0.99      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 4.01/0.99      inference(demodulation,[status(thm)],[c_11455,c_4800]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2962,plain,
% 4.01/0.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) != iProver_top
% 4.01/0.99      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) = iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_2958]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2964,plain,
% 4.01/0.99      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 4.01/0.99      | r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_2962]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1023,plain,
% 4.01/0.99      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) = iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1025,plain,
% 4.01/0.99      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_1023]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(contradiction,plain,
% 4.01/0.99      ( $false ),
% 4.01/0.99      inference(minisat,[status(thm)],[c_11476,c_11450,c_2964,c_1025]) ).
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/0.99  
% 4.01/0.99  ------                               Statistics
% 4.01/0.99  
% 4.01/0.99  ------ Selected
% 4.01/0.99  
% 4.01/0.99  total_time:                             0.494
% 4.01/0.99  
%------------------------------------------------------------------------------
