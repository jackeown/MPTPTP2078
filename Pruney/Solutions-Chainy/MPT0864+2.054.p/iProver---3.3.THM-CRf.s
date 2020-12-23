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
% DateTime   : Thu Dec  3 11:57:56 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 793 expanded)
%              Number of clauses        :   49 (  91 expanded)
%              Number of leaves         :   23 ( 247 expanded)
%              Depth                    :   18
%              Number of atoms          :  370 (1425 expanded)
%              Number of equality atoms :  300 (1268 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f25,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f20])).

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

fof(f18,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
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
    inference(nnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

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

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f81])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f82])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f86])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    ! [X2,X0,X1] : k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f56,f82,f86,f82])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
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

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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
      | k5_enumset1(X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f72,f48])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f97])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    ! [X2,X0,X1] : k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f57,f82,f82,f86])).

fof(f14,axiom,(
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
    inference(nnf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f74,f82])).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f84])).

fof(f93,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f54,f85,f86,f86,f86])).

fof(f98,plain,(
    ! [X1] : k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f84])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f82])).

fof(f87,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f83])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f42,f85,f83])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_29,negated_conjecture,
    ( k1_mcart_1(sK2) = sK2
    | k2_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,negated_conjecture,
    ( k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_28,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3432,plain,
    ( k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_30,c_28])).

cnf(c_3434,plain,
    ( k2_mcart_1(sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_29,c_3432])).

cnf(c_27,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3429,plain,
    ( k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_30,c_27])).

cnf(c_3436,plain,
    ( sK4 = sK2
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_3434,c_3429])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3239,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4482,plain,
    ( k2_zfmisc_1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_30,c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3237,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6165,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0) = k1_xboole_0
    | r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4482,c_3237])).

cnf(c_11565,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | r2_hidden(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3239,c_6165])).

cnf(c_11568,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | r2_hidden(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11565,c_30])).

cnf(c_12417,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | sK3 = sK2
    | r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3436,c_11568])).

cnf(c_23,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X5,X6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_26,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k5_enumset1(X5,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1287,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | X11 != X12
    | k5_enumset1(X4,X4,X5,X7,X9,X11,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_1288,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ),
    inference(unflattening,[status(thm)],[c_1287])).

cnf(c_1289,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_1291,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1289])).

cnf(c_3561,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5))
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3565,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) != iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3561])).

cnf(c_3567,plain,
    ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3565])).

cnf(c_9,plain,
    ( k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3695,plain,
    ( k5_enumset1(k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),sK2) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_30,c_9])).

cnf(c_3805,plain,
    ( k2_zfmisc_1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_30,c_3695])).

cnf(c_6163,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3805,c_3237])).

cnf(c_6938,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | sK3 = sK2
    | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3436,c_6163])).

cnf(c_12420,plain,
    ( sK3 = sK2
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12417,c_1291,c_3567,c_6938])).

cnf(c_12421,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | sK3 = sK2 ),
    inference(renaming,[status(thm)],[c_12420])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1,plain,
    ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3358,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_8,c_1])).

cnf(c_0,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3614,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_3615,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3614,c_1])).

cnf(c_14564,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3358,c_3615])).

cnf(c_14569,plain,
    ( sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_12421,c_14564])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3236,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4753,plain,
    ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3805,c_3236])).

cnf(c_14915,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14569,c_4753])).

cnf(c_14566,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14564])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14915,c_14566,c_3567,c_1291])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 6.59/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.59/1.53  
% 6.59/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.59/1.53  
% 6.59/1.53  ------  iProver source info
% 6.59/1.53  
% 6.59/1.53  git: date: 2020-06-30 10:37:57 +0100
% 6.59/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.59/1.53  git: non_committed_changes: false
% 6.59/1.53  git: last_make_outside_of_git: false
% 6.59/1.53  
% 6.59/1.53  ------ 
% 6.59/1.53  
% 6.59/1.53  ------ Input Options
% 6.59/1.53  
% 6.59/1.53  --out_options                           all
% 6.59/1.53  --tptp_safe_out                         true
% 6.59/1.53  --problem_path                          ""
% 6.59/1.53  --include_path                          ""
% 6.59/1.53  --clausifier                            res/vclausify_rel
% 6.59/1.53  --clausifier_options                    --mode clausify
% 6.59/1.53  --stdin                                 false
% 6.59/1.53  --stats_out                             all
% 6.59/1.53  
% 6.59/1.53  ------ General Options
% 6.59/1.53  
% 6.59/1.53  --fof                                   false
% 6.59/1.53  --time_out_real                         305.
% 6.59/1.53  --time_out_virtual                      -1.
% 6.59/1.53  --symbol_type_check                     false
% 6.59/1.53  --clausify_out                          false
% 6.59/1.53  --sig_cnt_out                           false
% 6.59/1.54  --trig_cnt_out                          false
% 6.59/1.54  --trig_cnt_out_tolerance                1.
% 6.59/1.54  --trig_cnt_out_sk_spl                   false
% 6.59/1.54  --abstr_cl_out                          false
% 6.59/1.54  
% 6.59/1.54  ------ Global Options
% 6.59/1.54  
% 6.59/1.54  --schedule                              default
% 6.59/1.54  --add_important_lit                     false
% 6.59/1.54  --prop_solver_per_cl                    1000
% 6.59/1.54  --min_unsat_core                        false
% 6.59/1.54  --soft_assumptions                      false
% 6.59/1.54  --soft_lemma_size                       3
% 6.59/1.54  --prop_impl_unit_size                   0
% 6.59/1.54  --prop_impl_unit                        []
% 6.59/1.54  --share_sel_clauses                     true
% 6.59/1.54  --reset_solvers                         false
% 6.59/1.54  --bc_imp_inh                            [conj_cone]
% 6.59/1.54  --conj_cone_tolerance                   3.
% 6.59/1.54  --extra_neg_conj                        none
% 6.59/1.54  --large_theory_mode                     true
% 6.59/1.54  --prolific_symb_bound                   200
% 6.59/1.54  --lt_threshold                          2000
% 6.59/1.54  --clause_weak_htbl                      true
% 6.59/1.54  --gc_record_bc_elim                     false
% 6.59/1.54  
% 6.59/1.54  ------ Preprocessing Options
% 6.59/1.54  
% 6.59/1.54  --preprocessing_flag                    true
% 6.59/1.54  --time_out_prep_mult                    0.1
% 6.59/1.54  --splitting_mode                        input
% 6.59/1.54  --splitting_grd                         true
% 6.59/1.54  --splitting_cvd                         false
% 6.59/1.54  --splitting_cvd_svl                     false
% 6.59/1.54  --splitting_nvd                         32
% 6.59/1.54  --sub_typing                            true
% 6.59/1.54  --prep_gs_sim                           true
% 6.59/1.54  --prep_unflatten                        true
% 6.59/1.54  --prep_res_sim                          true
% 6.59/1.54  --prep_upred                            true
% 6.59/1.54  --prep_sem_filter                       exhaustive
% 6.59/1.54  --prep_sem_filter_out                   false
% 6.59/1.54  --pred_elim                             true
% 6.59/1.54  --res_sim_input                         true
% 6.59/1.54  --eq_ax_congr_red                       true
% 6.59/1.54  --pure_diseq_elim                       true
% 6.59/1.54  --brand_transform                       false
% 6.59/1.54  --non_eq_to_eq                          false
% 6.59/1.54  --prep_def_merge                        true
% 6.59/1.54  --prep_def_merge_prop_impl              false
% 6.59/1.54  --prep_def_merge_mbd                    true
% 6.59/1.54  --prep_def_merge_tr_red                 false
% 6.59/1.54  --prep_def_merge_tr_cl                  false
% 6.59/1.54  --smt_preprocessing                     true
% 6.59/1.54  --smt_ac_axioms                         fast
% 6.59/1.54  --preprocessed_out                      false
% 6.59/1.54  --preprocessed_stats                    false
% 6.59/1.54  
% 6.59/1.54  ------ Abstraction refinement Options
% 6.59/1.54  
% 6.59/1.54  --abstr_ref                             []
% 6.59/1.54  --abstr_ref_prep                        false
% 6.59/1.54  --abstr_ref_until_sat                   false
% 6.59/1.54  --abstr_ref_sig_restrict                funpre
% 6.59/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.59/1.54  --abstr_ref_under                       []
% 6.59/1.54  
% 6.59/1.54  ------ SAT Options
% 6.59/1.54  
% 6.59/1.54  --sat_mode                              false
% 6.59/1.54  --sat_fm_restart_options                ""
% 6.59/1.54  --sat_gr_def                            false
% 6.59/1.54  --sat_epr_types                         true
% 6.59/1.54  --sat_non_cyclic_types                  false
% 6.59/1.54  --sat_finite_models                     false
% 6.59/1.54  --sat_fm_lemmas                         false
% 6.59/1.54  --sat_fm_prep                           false
% 6.59/1.54  --sat_fm_uc_incr                        true
% 6.59/1.54  --sat_out_model                         small
% 6.59/1.54  --sat_out_clauses                       false
% 6.59/1.54  
% 6.59/1.54  ------ QBF Options
% 6.59/1.54  
% 6.59/1.54  --qbf_mode                              false
% 6.59/1.54  --qbf_elim_univ                         false
% 6.59/1.54  --qbf_dom_inst                          none
% 6.59/1.54  --qbf_dom_pre_inst                      false
% 6.59/1.54  --qbf_sk_in                             false
% 6.59/1.54  --qbf_pred_elim                         true
% 6.59/1.54  --qbf_split                             512
% 6.59/1.54  
% 6.59/1.54  ------ BMC1 Options
% 6.59/1.54  
% 6.59/1.54  --bmc1_incremental                      false
% 6.59/1.54  --bmc1_axioms                           reachable_all
% 6.59/1.54  --bmc1_min_bound                        0
% 6.59/1.54  --bmc1_max_bound                        -1
% 6.59/1.54  --bmc1_max_bound_default                -1
% 6.59/1.54  --bmc1_symbol_reachability              true
% 6.59/1.54  --bmc1_property_lemmas                  false
% 6.59/1.54  --bmc1_k_induction                      false
% 6.59/1.54  --bmc1_non_equiv_states                 false
% 6.59/1.54  --bmc1_deadlock                         false
% 6.59/1.54  --bmc1_ucm                              false
% 6.59/1.54  --bmc1_add_unsat_core                   none
% 6.59/1.54  --bmc1_unsat_core_children              false
% 6.59/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.59/1.54  --bmc1_out_stat                         full
% 6.59/1.54  --bmc1_ground_init                      false
% 6.59/1.54  --bmc1_pre_inst_next_state              false
% 6.59/1.54  --bmc1_pre_inst_state                   false
% 6.59/1.54  --bmc1_pre_inst_reach_state             false
% 6.59/1.54  --bmc1_out_unsat_core                   false
% 6.59/1.54  --bmc1_aig_witness_out                  false
% 6.59/1.54  --bmc1_verbose                          false
% 6.59/1.54  --bmc1_dump_clauses_tptp                false
% 6.59/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.59/1.54  --bmc1_dump_file                        -
% 6.59/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.59/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.59/1.54  --bmc1_ucm_extend_mode                  1
% 6.59/1.54  --bmc1_ucm_init_mode                    2
% 6.59/1.54  --bmc1_ucm_cone_mode                    none
% 6.59/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.59/1.54  --bmc1_ucm_relax_model                  4
% 6.59/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.59/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.59/1.54  --bmc1_ucm_layered_model                none
% 6.59/1.54  --bmc1_ucm_max_lemma_size               10
% 6.59/1.54  
% 6.59/1.54  ------ AIG Options
% 6.59/1.54  
% 6.59/1.54  --aig_mode                              false
% 6.59/1.54  
% 6.59/1.54  ------ Instantiation Options
% 6.59/1.54  
% 6.59/1.54  --instantiation_flag                    true
% 6.59/1.54  --inst_sos_flag                         false
% 6.59/1.54  --inst_sos_phase                        true
% 6.59/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.59/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.59/1.54  --inst_lit_sel_side                     num_symb
% 6.59/1.54  --inst_solver_per_active                1400
% 6.59/1.54  --inst_solver_calls_frac                1.
% 6.59/1.54  --inst_passive_queue_type               priority_queues
% 6.59/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.59/1.54  --inst_passive_queues_freq              [25;2]
% 6.59/1.54  --inst_dismatching                      true
% 6.59/1.54  --inst_eager_unprocessed_to_passive     true
% 6.59/1.54  --inst_prop_sim_given                   true
% 6.59/1.54  --inst_prop_sim_new                     false
% 6.59/1.54  --inst_subs_new                         false
% 6.59/1.54  --inst_eq_res_simp                      false
% 6.59/1.54  --inst_subs_given                       false
% 6.59/1.54  --inst_orphan_elimination               true
% 6.59/1.54  --inst_learning_loop_flag               true
% 6.59/1.54  --inst_learning_start                   3000
% 6.59/1.54  --inst_learning_factor                  2
% 6.59/1.54  --inst_start_prop_sim_after_learn       3
% 6.59/1.54  --inst_sel_renew                        solver
% 6.59/1.54  --inst_lit_activity_flag                true
% 6.59/1.54  --inst_restr_to_given                   false
% 6.59/1.54  --inst_activity_threshold               500
% 6.59/1.54  --inst_out_proof                        true
% 6.59/1.54  
% 6.59/1.54  ------ Resolution Options
% 6.59/1.54  
% 6.59/1.54  --resolution_flag                       true
% 6.59/1.54  --res_lit_sel                           adaptive
% 6.59/1.54  --res_lit_sel_side                      none
% 6.59/1.54  --res_ordering                          kbo
% 6.59/1.54  --res_to_prop_solver                    active
% 6.59/1.54  --res_prop_simpl_new                    false
% 6.59/1.54  --res_prop_simpl_given                  true
% 6.59/1.54  --res_passive_queue_type                priority_queues
% 6.59/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.59/1.54  --res_passive_queues_freq               [15;5]
% 6.59/1.54  --res_forward_subs                      full
% 6.59/1.54  --res_backward_subs                     full
% 6.59/1.54  --res_forward_subs_resolution           true
% 6.59/1.54  --res_backward_subs_resolution          true
% 6.59/1.54  --res_orphan_elimination                true
% 6.59/1.54  --res_time_limit                        2.
% 6.59/1.54  --res_out_proof                         true
% 6.59/1.54  
% 6.59/1.54  ------ Superposition Options
% 6.59/1.54  
% 6.59/1.54  --superposition_flag                    true
% 6.59/1.54  --sup_passive_queue_type                priority_queues
% 6.59/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.59/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.59/1.54  --demod_completeness_check              fast
% 6.59/1.54  --demod_use_ground                      true
% 6.59/1.54  --sup_to_prop_solver                    passive
% 6.59/1.54  --sup_prop_simpl_new                    true
% 6.59/1.54  --sup_prop_simpl_given                  true
% 6.59/1.54  --sup_fun_splitting                     false
% 6.59/1.54  --sup_smt_interval                      50000
% 6.59/1.54  
% 6.59/1.54  ------ Superposition Simplification Setup
% 6.59/1.54  
% 6.59/1.54  --sup_indices_passive                   []
% 6.59/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.59/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.59/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.59/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.59/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.59/1.54  --sup_full_bw                           [BwDemod]
% 6.59/1.54  --sup_immed_triv                        [TrivRules]
% 6.59/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.59/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.59/1.54  --sup_immed_bw_main                     []
% 6.59/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.59/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.59/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.59/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.59/1.54  
% 6.59/1.54  ------ Combination Options
% 6.59/1.54  
% 6.59/1.54  --comb_res_mult                         3
% 6.59/1.54  --comb_sup_mult                         2
% 6.59/1.54  --comb_inst_mult                        10
% 6.59/1.54  
% 6.59/1.54  ------ Debug Options
% 6.59/1.54  
% 6.59/1.54  --dbg_backtrace                         false
% 6.59/1.54  --dbg_dump_prop_clauses                 false
% 6.59/1.54  --dbg_dump_prop_clauses_file            -
% 6.59/1.54  --dbg_out_stat                          false
% 6.59/1.54  ------ Parsing...
% 6.59/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.59/1.54  
% 6.59/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.59/1.54  
% 6.59/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.59/1.54  
% 6.59/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.59/1.54  ------ Proving...
% 6.59/1.54  ------ Problem Properties 
% 6.59/1.54  
% 6.59/1.54  
% 6.59/1.54  clauses                                 31
% 6.59/1.54  conjectures                             2
% 6.59/1.54  EPR                                     7
% 6.59/1.54  Horn                                    27
% 6.59/1.54  unary                                   10
% 6.59/1.54  binary                                  13
% 6.59/1.54  lits                                    70
% 6.59/1.54  lits eq                                 34
% 6.59/1.54  fd_pure                                 0
% 6.59/1.54  fd_pseudo                               0
% 6.59/1.54  fd_cond                                 2
% 6.59/1.54  fd_pseudo_cond                          3
% 6.59/1.54  AC symbols                              0
% 6.59/1.54  
% 6.59/1.54  ------ Schedule dynamic 5 is on 
% 6.59/1.54  
% 6.59/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.59/1.54  
% 6.59/1.54  
% 6.59/1.54  ------ 
% 6.59/1.54  Current options:
% 6.59/1.54  ------ 
% 6.59/1.54  
% 6.59/1.54  ------ Input Options
% 6.59/1.54  
% 6.59/1.54  --out_options                           all
% 6.59/1.54  --tptp_safe_out                         true
% 6.59/1.54  --problem_path                          ""
% 6.59/1.54  --include_path                          ""
% 6.59/1.54  --clausifier                            res/vclausify_rel
% 6.59/1.54  --clausifier_options                    --mode clausify
% 6.59/1.54  --stdin                                 false
% 6.59/1.54  --stats_out                             all
% 6.59/1.54  
% 6.59/1.54  ------ General Options
% 6.59/1.54  
% 6.59/1.54  --fof                                   false
% 6.59/1.54  --time_out_real                         305.
% 6.59/1.54  --time_out_virtual                      -1.
% 6.59/1.54  --symbol_type_check                     false
% 6.59/1.54  --clausify_out                          false
% 6.59/1.54  --sig_cnt_out                           false
% 6.59/1.54  --trig_cnt_out                          false
% 6.59/1.54  --trig_cnt_out_tolerance                1.
% 6.59/1.54  --trig_cnt_out_sk_spl                   false
% 6.59/1.54  --abstr_cl_out                          false
% 6.59/1.54  
% 6.59/1.54  ------ Global Options
% 6.59/1.54  
% 6.59/1.54  --schedule                              default
% 6.59/1.54  --add_important_lit                     false
% 6.59/1.54  --prop_solver_per_cl                    1000
% 6.59/1.54  --min_unsat_core                        false
% 6.59/1.54  --soft_assumptions                      false
% 6.59/1.54  --soft_lemma_size                       3
% 6.59/1.54  --prop_impl_unit_size                   0
% 6.59/1.54  --prop_impl_unit                        []
% 6.59/1.54  --share_sel_clauses                     true
% 6.59/1.54  --reset_solvers                         false
% 6.59/1.54  --bc_imp_inh                            [conj_cone]
% 6.59/1.54  --conj_cone_tolerance                   3.
% 6.59/1.54  --extra_neg_conj                        none
% 6.59/1.54  --large_theory_mode                     true
% 6.59/1.54  --prolific_symb_bound                   200
% 6.59/1.54  --lt_threshold                          2000
% 6.59/1.54  --clause_weak_htbl                      true
% 6.59/1.54  --gc_record_bc_elim                     false
% 6.59/1.54  
% 6.59/1.54  ------ Preprocessing Options
% 6.59/1.54  
% 6.59/1.54  --preprocessing_flag                    true
% 6.59/1.54  --time_out_prep_mult                    0.1
% 6.59/1.54  --splitting_mode                        input
% 6.59/1.54  --splitting_grd                         true
% 6.59/1.54  --splitting_cvd                         false
% 6.59/1.54  --splitting_cvd_svl                     false
% 6.59/1.54  --splitting_nvd                         32
% 6.59/1.54  --sub_typing                            true
% 6.59/1.54  --prep_gs_sim                           true
% 6.59/1.54  --prep_unflatten                        true
% 6.59/1.54  --prep_res_sim                          true
% 6.59/1.54  --prep_upred                            true
% 6.59/1.54  --prep_sem_filter                       exhaustive
% 6.59/1.54  --prep_sem_filter_out                   false
% 6.59/1.54  --pred_elim                             true
% 6.59/1.54  --res_sim_input                         true
% 6.59/1.54  --eq_ax_congr_red                       true
% 6.59/1.54  --pure_diseq_elim                       true
% 6.59/1.54  --brand_transform                       false
% 6.59/1.54  --non_eq_to_eq                          false
% 6.59/1.54  --prep_def_merge                        true
% 6.59/1.54  --prep_def_merge_prop_impl              false
% 6.59/1.54  --prep_def_merge_mbd                    true
% 6.59/1.54  --prep_def_merge_tr_red                 false
% 6.59/1.54  --prep_def_merge_tr_cl                  false
% 6.59/1.54  --smt_preprocessing                     true
% 6.59/1.54  --smt_ac_axioms                         fast
% 6.59/1.54  --preprocessed_out                      false
% 6.59/1.54  --preprocessed_stats                    false
% 6.59/1.54  
% 6.59/1.54  ------ Abstraction refinement Options
% 6.59/1.54  
% 6.59/1.54  --abstr_ref                             []
% 6.59/1.54  --abstr_ref_prep                        false
% 6.59/1.54  --abstr_ref_until_sat                   false
% 6.59/1.54  --abstr_ref_sig_restrict                funpre
% 6.59/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 6.59/1.54  --abstr_ref_under                       []
% 6.59/1.54  
% 6.59/1.54  ------ SAT Options
% 6.59/1.54  
% 6.59/1.54  --sat_mode                              false
% 6.59/1.54  --sat_fm_restart_options                ""
% 6.59/1.54  --sat_gr_def                            false
% 6.59/1.54  --sat_epr_types                         true
% 6.59/1.54  --sat_non_cyclic_types                  false
% 6.59/1.54  --sat_finite_models                     false
% 6.59/1.54  --sat_fm_lemmas                         false
% 6.59/1.54  --sat_fm_prep                           false
% 6.59/1.54  --sat_fm_uc_incr                        true
% 6.59/1.54  --sat_out_model                         small
% 6.59/1.54  --sat_out_clauses                       false
% 6.59/1.54  
% 6.59/1.54  ------ QBF Options
% 6.59/1.54  
% 6.59/1.54  --qbf_mode                              false
% 6.59/1.54  --qbf_elim_univ                         false
% 6.59/1.54  --qbf_dom_inst                          none
% 6.59/1.54  --qbf_dom_pre_inst                      false
% 6.59/1.54  --qbf_sk_in                             false
% 6.59/1.54  --qbf_pred_elim                         true
% 6.59/1.54  --qbf_split                             512
% 6.59/1.54  
% 6.59/1.54  ------ BMC1 Options
% 6.59/1.54  
% 6.59/1.54  --bmc1_incremental                      false
% 6.59/1.54  --bmc1_axioms                           reachable_all
% 6.59/1.54  --bmc1_min_bound                        0
% 6.59/1.54  --bmc1_max_bound                        -1
% 6.59/1.54  --bmc1_max_bound_default                -1
% 6.59/1.54  --bmc1_symbol_reachability              true
% 6.59/1.54  --bmc1_property_lemmas                  false
% 6.59/1.54  --bmc1_k_induction                      false
% 6.59/1.54  --bmc1_non_equiv_states                 false
% 6.59/1.54  --bmc1_deadlock                         false
% 6.59/1.54  --bmc1_ucm                              false
% 6.59/1.54  --bmc1_add_unsat_core                   none
% 6.59/1.54  --bmc1_unsat_core_children              false
% 6.59/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 6.59/1.54  --bmc1_out_stat                         full
% 6.59/1.54  --bmc1_ground_init                      false
% 6.59/1.54  --bmc1_pre_inst_next_state              false
% 6.59/1.54  --bmc1_pre_inst_state                   false
% 6.59/1.54  --bmc1_pre_inst_reach_state             false
% 6.59/1.54  --bmc1_out_unsat_core                   false
% 6.59/1.54  --bmc1_aig_witness_out                  false
% 6.59/1.54  --bmc1_verbose                          false
% 6.59/1.54  --bmc1_dump_clauses_tptp                false
% 6.59/1.54  --bmc1_dump_unsat_core_tptp             false
% 6.59/1.54  --bmc1_dump_file                        -
% 6.59/1.54  --bmc1_ucm_expand_uc_limit              128
% 6.59/1.54  --bmc1_ucm_n_expand_iterations          6
% 6.59/1.54  --bmc1_ucm_extend_mode                  1
% 6.59/1.54  --bmc1_ucm_init_mode                    2
% 6.59/1.54  --bmc1_ucm_cone_mode                    none
% 6.59/1.54  --bmc1_ucm_reduced_relation_type        0
% 6.59/1.54  --bmc1_ucm_relax_model                  4
% 6.59/1.54  --bmc1_ucm_full_tr_after_sat            true
% 6.59/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 6.59/1.54  --bmc1_ucm_layered_model                none
% 6.59/1.54  --bmc1_ucm_max_lemma_size               10
% 6.59/1.54  
% 6.59/1.54  ------ AIG Options
% 6.59/1.54  
% 6.59/1.54  --aig_mode                              false
% 6.59/1.54  
% 6.59/1.54  ------ Instantiation Options
% 6.59/1.54  
% 6.59/1.54  --instantiation_flag                    true
% 6.59/1.54  --inst_sos_flag                         false
% 6.59/1.54  --inst_sos_phase                        true
% 6.59/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.59/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.59/1.54  --inst_lit_sel_side                     none
% 6.59/1.54  --inst_solver_per_active                1400
% 6.59/1.54  --inst_solver_calls_frac                1.
% 6.59/1.54  --inst_passive_queue_type               priority_queues
% 6.59/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.59/1.54  --inst_passive_queues_freq              [25;2]
% 6.59/1.54  --inst_dismatching                      true
% 6.59/1.54  --inst_eager_unprocessed_to_passive     true
% 6.59/1.54  --inst_prop_sim_given                   true
% 6.59/1.54  --inst_prop_sim_new                     false
% 6.59/1.54  --inst_subs_new                         false
% 6.59/1.54  --inst_eq_res_simp                      false
% 6.59/1.54  --inst_subs_given                       false
% 6.59/1.54  --inst_orphan_elimination               true
% 6.59/1.54  --inst_learning_loop_flag               true
% 6.59/1.54  --inst_learning_start                   3000
% 6.59/1.54  --inst_learning_factor                  2
% 6.59/1.54  --inst_start_prop_sim_after_learn       3
% 6.59/1.54  --inst_sel_renew                        solver
% 6.59/1.54  --inst_lit_activity_flag                true
% 6.59/1.54  --inst_restr_to_given                   false
% 6.59/1.54  --inst_activity_threshold               500
% 6.59/1.54  --inst_out_proof                        true
% 6.59/1.54  
% 6.59/1.54  ------ Resolution Options
% 6.59/1.54  
% 6.59/1.54  --resolution_flag                       false
% 6.59/1.54  --res_lit_sel                           adaptive
% 6.59/1.54  --res_lit_sel_side                      none
% 6.59/1.54  --res_ordering                          kbo
% 6.59/1.54  --res_to_prop_solver                    active
% 6.59/1.54  --res_prop_simpl_new                    false
% 6.59/1.54  --res_prop_simpl_given                  true
% 6.59/1.54  --res_passive_queue_type                priority_queues
% 6.59/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.59/1.54  --res_passive_queues_freq               [15;5]
% 6.59/1.54  --res_forward_subs                      full
% 6.59/1.54  --res_backward_subs                     full
% 6.59/1.54  --res_forward_subs_resolution           true
% 6.59/1.54  --res_backward_subs_resolution          true
% 6.59/1.54  --res_orphan_elimination                true
% 6.59/1.54  --res_time_limit                        2.
% 6.59/1.54  --res_out_proof                         true
% 6.59/1.54  
% 6.59/1.54  ------ Superposition Options
% 6.59/1.54  
% 6.59/1.54  --superposition_flag                    true
% 6.59/1.54  --sup_passive_queue_type                priority_queues
% 6.59/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.59/1.54  --sup_passive_queues_freq               [8;1;4]
% 6.59/1.54  --demod_completeness_check              fast
% 6.59/1.54  --demod_use_ground                      true
% 6.59/1.54  --sup_to_prop_solver                    passive
% 6.59/1.54  --sup_prop_simpl_new                    true
% 6.59/1.54  --sup_prop_simpl_given                  true
% 6.59/1.54  --sup_fun_splitting                     false
% 6.59/1.54  --sup_smt_interval                      50000
% 6.59/1.54  
% 6.59/1.54  ------ Superposition Simplification Setup
% 6.59/1.54  
% 6.59/1.54  --sup_indices_passive                   []
% 6.59/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.59/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.59/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.59/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 6.59/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.59/1.54  --sup_full_bw                           [BwDemod]
% 6.59/1.54  --sup_immed_triv                        [TrivRules]
% 6.59/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.59/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.59/1.54  --sup_immed_bw_main                     []
% 6.59/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.59/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 6.59/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.59/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.59/1.54  
% 6.59/1.54  ------ Combination Options
% 6.59/1.54  
% 6.59/1.54  --comb_res_mult                         3
% 6.59/1.54  --comb_sup_mult                         2
% 6.59/1.54  --comb_inst_mult                        10
% 6.59/1.54  
% 6.59/1.54  ------ Debug Options
% 6.59/1.54  
% 6.59/1.54  --dbg_backtrace                         false
% 6.59/1.54  --dbg_dump_prop_clauses                 false
% 6.59/1.54  --dbg_dump_prop_clauses_file            -
% 6.59/1.54  --dbg_out_stat                          false
% 6.59/1.54  
% 6.59/1.54  
% 6.59/1.54  
% 6.59/1.54  
% 6.59/1.54  ------ Proving...
% 6.59/1.54  
% 6.59/1.54  
% 6.59/1.54  % SZS status Theorem for theBenchmark.p
% 6.59/1.54  
% 6.59/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 6.59/1.54  
% 6.59/1.54  fof(f19,conjecture,(
% 6.59/1.54    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f20,negated_conjecture,(
% 6.59/1.54    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 6.59/1.54    inference(negated_conjecture,[],[f19])).
% 6.59/1.54  
% 6.59/1.54  fof(f25,plain,(
% 6.59/1.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 6.59/1.54    inference(ennf_transformation,[],[f20])).
% 6.59/1.54  
% 6.59/1.54  fof(f37,plain,(
% 6.59/1.54    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK3,sK4) = X0) )),
% 6.59/1.54    introduced(choice_axiom,[])).
% 6.59/1.54  
% 6.59/1.54  fof(f36,plain,(
% 6.59/1.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 6.59/1.54    introduced(choice_axiom,[])).
% 6.59/1.54  
% 6.59/1.54  fof(f38,plain,(
% 6.59/1.54    (k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & k4_tarski(sK3,sK4) = sK2),
% 6.59/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f37,f36])).
% 6.59/1.54  
% 6.59/1.54  fof(f78,plain,(
% 6.59/1.54    k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2),
% 6.59/1.54    inference(cnf_transformation,[],[f38])).
% 6.59/1.54  
% 6.59/1.54  fof(f77,plain,(
% 6.59/1.54    k4_tarski(sK3,sK4) = sK2),
% 6.59/1.54    inference(cnf_transformation,[],[f38])).
% 6.59/1.54  
% 6.59/1.54  fof(f18,axiom,(
% 6.59/1.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f75,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 6.59/1.54    inference(cnf_transformation,[],[f18])).
% 6.59/1.54  
% 6.59/1.54  fof(f76,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 6.59/1.54    inference(cnf_transformation,[],[f18])).
% 6.59/1.54  
% 6.59/1.54  fof(f11,axiom,(
% 6.59/1.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f28,plain,(
% 6.59/1.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 6.59/1.54    inference(nnf_transformation,[],[f11])).
% 6.59/1.54  
% 6.59/1.54  fof(f50,plain,(
% 6.59/1.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.59/1.54    inference(cnf_transformation,[],[f28])).
% 6.59/1.54  
% 6.59/1.54  fof(f5,axiom,(
% 6.59/1.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f43,plain,(
% 6.59/1.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.59/1.54    inference(cnf_transformation,[],[f5])).
% 6.59/1.54  
% 6.59/1.54  fof(f6,axiom,(
% 6.59/1.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f44,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.59/1.54    inference(cnf_transformation,[],[f6])).
% 6.59/1.54  
% 6.59/1.54  fof(f7,axiom,(
% 6.59/1.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f45,plain,(
% 6.59/1.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.59/1.54    inference(cnf_transformation,[],[f7])).
% 6.59/1.54  
% 6.59/1.54  fof(f8,axiom,(
% 6.59/1.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f46,plain,(
% 6.59/1.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.59/1.54    inference(cnf_transformation,[],[f8])).
% 6.59/1.54  
% 6.59/1.54  fof(f9,axiom,(
% 6.59/1.54    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f47,plain,(
% 6.59/1.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.59/1.54    inference(cnf_transformation,[],[f9])).
% 6.59/1.54  
% 6.59/1.54  fof(f10,axiom,(
% 6.59/1.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f48,plain,(
% 6.59/1.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.59/1.54    inference(cnf_transformation,[],[f10])).
% 6.59/1.54  
% 6.59/1.54  fof(f79,plain,(
% 6.59/1.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 6.59/1.54    inference(definition_unfolding,[],[f47,f48])).
% 6.59/1.54  
% 6.59/1.54  fof(f80,plain,(
% 6.59/1.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 6.59/1.54    inference(definition_unfolding,[],[f46,f79])).
% 6.59/1.54  
% 6.59/1.54  fof(f81,plain,(
% 6.59/1.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 6.59/1.54    inference(definition_unfolding,[],[f45,f80])).
% 6.59/1.54  
% 6.59/1.54  fof(f82,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 6.59/1.54    inference(definition_unfolding,[],[f44,f81])).
% 6.59/1.54  
% 6.59/1.54  fof(f86,plain,(
% 6.59/1.54    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 6.59/1.54    inference(definition_unfolding,[],[f43,f82])).
% 6.59/1.54  
% 6.59/1.54  fof(f90,plain,(
% 6.59/1.54    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.59/1.54    inference(definition_unfolding,[],[f50,f86])).
% 6.59/1.54  
% 6.59/1.54  fof(f15,axiom,(
% 6.59/1.54    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f56,plain,(
% 6.59/1.54    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 6.59/1.54    inference(cnf_transformation,[],[f15])).
% 6.59/1.54  
% 6.59/1.54  fof(f95,plain,(
% 6.59/1.54    ( ! [X2,X0,X1] : (k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 6.59/1.54    inference(definition_unfolding,[],[f56,f82,f86,f82])).
% 6.59/1.54  
% 6.59/1.54  fof(f13,axiom,(
% 6.59/1.54    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f23,plain,(
% 6.59/1.54    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 6.59/1.54    inference(ennf_transformation,[],[f13])).
% 6.59/1.54  
% 6.59/1.54  fof(f53,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 6.59/1.54    inference(cnf_transformation,[],[f23])).
% 6.59/1.54  
% 6.59/1.54  fof(f26,plain,(
% 6.59/1.54    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 6.59/1.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.59/1.54  
% 6.59/1.54  fof(f30,plain,(
% 6.59/1.54    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 6.59/1.54    inference(nnf_transformation,[],[f26])).
% 6.59/1.54  
% 6.59/1.54  fof(f31,plain,(
% 6.59/1.54    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 6.59/1.54    inference(flattening,[],[f30])).
% 6.59/1.54  
% 6.59/1.54  fof(f32,plain,(
% 6.59/1.54    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 6.59/1.54    inference(rectify,[],[f31])).
% 6.59/1.54  
% 6.59/1.54  fof(f33,plain,(
% 6.59/1.54    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 6.59/1.54    introduced(choice_axiom,[])).
% 6.59/1.54  
% 6.59/1.54  fof(f34,plain,(
% 6.59/1.54    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 6.59/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 6.59/1.54  
% 6.59/1.54  fof(f59,plain,(
% 6.59/1.54    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 6.59/1.54    inference(cnf_transformation,[],[f34])).
% 6.59/1.54  
% 6.59/1.54  fof(f104,plain,(
% 6.59/1.54    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X0,X1,X2,X3,X4,X8,X6)) )),
% 6.59/1.54    inference(equality_resolution,[],[f59])).
% 6.59/1.54  
% 6.59/1.54  fof(f16,axiom,(
% 6.59/1.54    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f24,plain,(
% 6.59/1.54    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 6.59/1.54    inference(ennf_transformation,[],[f16])).
% 6.59/1.54  
% 6.59/1.54  fof(f27,plain,(
% 6.59/1.54    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 6.59/1.54    inference(definition_folding,[],[f24,f26])).
% 6.59/1.54  
% 6.59/1.54  fof(f35,plain,(
% 6.59/1.54    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 6.59/1.54    inference(nnf_transformation,[],[f27])).
% 6.59/1.54  
% 6.59/1.54  fof(f72,plain,(
% 6.59/1.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 6.59/1.54    inference(cnf_transformation,[],[f35])).
% 6.59/1.54  
% 6.59/1.54  fof(f97,plain,(
% 6.59/1.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k5_enumset1(X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 6.59/1.54    inference(definition_unfolding,[],[f72,f48])).
% 6.59/1.54  
% 6.59/1.54  fof(f105,plain,(
% 6.59/1.54    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) )),
% 6.59/1.54    inference(equality_resolution,[],[f97])).
% 6.59/1.54  
% 6.59/1.54  fof(f57,plain,(
% 6.59/1.54    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 6.59/1.54    inference(cnf_transformation,[],[f15])).
% 6.59/1.54  
% 6.59/1.54  fof(f94,plain,(
% 6.59/1.54    ( ! [X2,X0,X1] : (k5_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) )),
% 6.59/1.54    inference(definition_unfolding,[],[f57,f82,f82,f86])).
% 6.59/1.54  
% 6.59/1.54  fof(f14,axiom,(
% 6.59/1.54    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f29,plain,(
% 6.59/1.54    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 6.59/1.54    inference(nnf_transformation,[],[f14])).
% 6.59/1.54  
% 6.59/1.54  fof(f54,plain,(
% 6.59/1.54    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 6.59/1.54    inference(cnf_transformation,[],[f29])).
% 6.59/1.54  
% 6.59/1.54  fof(f3,axiom,(
% 6.59/1.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f41,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.59/1.54    inference(cnf_transformation,[],[f3])).
% 6.59/1.54  
% 6.59/1.54  fof(f17,axiom,(
% 6.59/1.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f74,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.59/1.54    inference(cnf_transformation,[],[f17])).
% 6.59/1.54  
% 6.59/1.54  fof(f84,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 6.59/1.54    inference(definition_unfolding,[],[f74,f82])).
% 6.59/1.54  
% 6.59/1.54  fof(f85,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 6.59/1.54    inference(definition_unfolding,[],[f41,f84])).
% 6.59/1.54  
% 6.59/1.54  fof(f93,plain,(
% 6.59/1.54    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 6.59/1.54    inference(definition_unfolding,[],[f54,f85,f86,f86,f86])).
% 6.59/1.54  
% 6.59/1.54  fof(f98,plain,(
% 6.59/1.54    ( ! [X1] : (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) )),
% 6.59/1.54    inference(equality_resolution,[],[f93])).
% 6.59/1.54  
% 6.59/1.54  fof(f2,axiom,(
% 6.59/1.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f22,plain,(
% 6.59/1.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 6.59/1.54    inference(rectify,[],[f2])).
% 6.59/1.54  
% 6.59/1.54  fof(f40,plain,(
% 6.59/1.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.59/1.54    inference(cnf_transformation,[],[f22])).
% 6.59/1.54  
% 6.59/1.54  fof(f88,plain,(
% 6.59/1.54    ( ! [X0] : (k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 6.59/1.54    inference(definition_unfolding,[],[f40,f84])).
% 6.59/1.54  
% 6.59/1.54  fof(f1,axiom,(
% 6.59/1.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f21,plain,(
% 6.59/1.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 6.59/1.54    inference(rectify,[],[f1])).
% 6.59/1.54  
% 6.59/1.54  fof(f39,plain,(
% 6.59/1.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 6.59/1.54    inference(cnf_transformation,[],[f21])).
% 6.59/1.54  
% 6.59/1.54  fof(f12,axiom,(
% 6.59/1.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f51,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.59/1.54    inference(cnf_transformation,[],[f12])).
% 6.59/1.54  
% 6.59/1.54  fof(f83,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 6.59/1.54    inference(definition_unfolding,[],[f51,f82])).
% 6.59/1.54  
% 6.59/1.54  fof(f87,plain,(
% 6.59/1.54    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 6.59/1.54    inference(definition_unfolding,[],[f39,f83])).
% 6.59/1.54  
% 6.59/1.54  fof(f4,axiom,(
% 6.59/1.54    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 6.59/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.59/1.54  
% 6.59/1.54  fof(f42,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 6.59/1.54    inference(cnf_transformation,[],[f4])).
% 6.59/1.54  
% 6.59/1.54  fof(f89,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0) )),
% 6.59/1.54    inference(definition_unfolding,[],[f42,f85,f83])).
% 6.59/1.54  
% 6.59/1.54  fof(f52,plain,(
% 6.59/1.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 6.59/1.54    inference(cnf_transformation,[],[f23])).
% 6.59/1.54  
% 6.59/1.54  cnf(c_29,negated_conjecture,
% 6.59/1.54      ( k1_mcart_1(sK2) = sK2 | k2_mcart_1(sK2) = sK2 ),
% 6.59/1.54      inference(cnf_transformation,[],[f78]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_30,negated_conjecture,
% 6.59/1.54      ( k4_tarski(sK3,sK4) = sK2 ),
% 6.59/1.54      inference(cnf_transformation,[],[f77]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_28,plain,
% 6.59/1.54      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 6.59/1.54      inference(cnf_transformation,[],[f75]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3432,plain,
% 6.59/1.54      ( k1_mcart_1(sK2) = sK3 ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_30,c_28]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3434,plain,
% 6.59/1.54      ( k2_mcart_1(sK2) = sK2 | sK3 = sK2 ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_29,c_3432]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_27,plain,
% 6.59/1.54      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 6.59/1.54      inference(cnf_transformation,[],[f76]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3429,plain,
% 6.59/1.54      ( k2_mcart_1(sK2) = sK4 ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_30,c_27]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3436,plain,
% 6.59/1.54      ( sK4 = sK2 | sK3 = sK2 ),
% 6.59/1.54      inference(demodulation,[status(thm)],[c_3434,c_3429]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3,plain,
% 6.59/1.54      ( ~ r2_hidden(X0,X1)
% 6.59/1.54      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) ),
% 6.59/1.54      inference(cnf_transformation,[],[f90]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3239,plain,
% 6.59/1.54      ( r2_hidden(X0,X1) != iProver_top
% 6.59/1.54      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 6.59/1.54      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_10,plain,
% 6.59/1.54      ( k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
% 6.59/1.54      inference(cnf_transformation,[],[f95]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_4482,plain,
% 6.59/1.54      ( k2_zfmisc_1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0)) ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_30,c_10]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_5,plain,
% 6.59/1.54      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 6.59/1.54      inference(cnf_transformation,[],[f53]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3237,plain,
% 6.59/1.54      ( k1_xboole_0 = X0
% 6.59/1.54      | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 6.59/1.54      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_6165,plain,
% 6.59/1.54      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0) = k1_xboole_0
% 6.59/1.54      | r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,X0))) != iProver_top ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_4482,c_3237]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_11565,plain,
% 6.59/1.54      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 6.59/1.54      | r2_hidden(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k4_tarski(sK3,sK4))) != iProver_top ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_3239,c_6165]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_11568,plain,
% 6.59/1.54      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 6.59/1.54      | r2_hidden(sK4,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 6.59/1.54      inference(light_normalisation,[status(thm)],[c_11565,c_30]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_12417,plain,
% 6.59/1.54      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 6.59/1.54      | sK3 = sK2
% 6.59/1.54      | r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_3436,c_11568]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_23,plain,
% 6.59/1.54      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X5,X6) ),
% 6.59/1.54      inference(cnf_transformation,[],[f104]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_26,plain,
% 6.59/1.54      ( sP0(X0,X1,X2,X3,X4,X5,k5_enumset1(X5,X5,X4,X3,X2,X1,X0)) ),
% 6.59/1.54      inference(cnf_transformation,[],[f105]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_1287,plain,
% 6.59/1.54      ( r2_hidden(X0,X1)
% 6.59/1.54      | X2 != X3
% 6.59/1.54      | X4 != X0
% 6.59/1.54      | X5 != X6
% 6.59/1.54      | X7 != X8
% 6.59/1.54      | X9 != X10
% 6.59/1.54      | X11 != X12
% 6.59/1.54      | k5_enumset1(X4,X4,X5,X7,X9,X11,X2) != X1 ),
% 6.59/1.54      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_1288,plain,
% 6.59/1.54      ( r2_hidden(X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ),
% 6.59/1.54      inference(unflattening,[status(thm)],[c_1287]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_1289,plain,
% 6.59/1.54      ( r2_hidden(X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 6.59/1.54      inference(predicate_to_equality,[status(thm)],[c_1288]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_1291,plain,
% 6.59/1.54      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 6.59/1.54      inference(instantiation,[status(thm)],[c_1289]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3561,plain,
% 6.59/1.54      ( ~ r2_hidden(X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5))
% 6.59/1.54      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ),
% 6.59/1.54      inference(instantiation,[status(thm)],[c_3]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3565,plain,
% 6.59/1.54      ( r2_hidden(X0,k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) != iProver_top
% 6.59/1.54      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 6.59/1.54      inference(predicate_to_equality,[status(thm)],[c_3561]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3567,plain,
% 6.59/1.54      ( r2_hidden(sK2,k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top
% 6.59/1.54      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 6.59/1.54      inference(instantiation,[status(thm)],[c_3565]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_9,plain,
% 6.59/1.54      ( k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
% 6.59/1.54      inference(cnf_transformation,[],[f94]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3695,plain,
% 6.59/1.54      ( k5_enumset1(k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),k4_tarski(X0,sK4),sK2) = k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_30,c_9]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3805,plain,
% 6.59/1.54      ( k2_zfmisc_1(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_30,c_3695]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_6163,plain,
% 6.59/1.54      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 6.59/1.54      | r1_tarski(k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_3805,c_3237]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_6938,plain,
% 6.59/1.54      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 6.59/1.54      | sK3 = sK2
% 6.59/1.54      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_3436,c_6163]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_12420,plain,
% 6.59/1.54      ( sK3 = sK2
% 6.59/1.54      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0 ),
% 6.59/1.54      inference(global_propositional_subsumption,
% 6.59/1.54                [status(thm)],
% 6.59/1.54                [c_12417,c_1291,c_3567,c_6938]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_12421,plain,
% 6.59/1.54      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 6.59/1.54      | sK3 = sK2 ),
% 6.59/1.54      inference(renaming,[status(thm)],[c_12420]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_8,plain,
% 6.59/1.54      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 6.59/1.54      inference(cnf_transformation,[],[f98]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_1,plain,
% 6.59/1.54      ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 6.59/1.54      inference(cnf_transformation,[],[f88]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3358,plain,
% 6.59/1.54      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) != k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
% 6.59/1.54      inference(demodulation,[status(thm)],[c_8,c_1]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_0,plain,
% 6.59/1.54      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 6.59/1.54      inference(cnf_transformation,[],[f87]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_2,plain,
% 6.59/1.54      ( k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
% 6.59/1.54      inference(cnf_transformation,[],[f89]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3614,plain,
% 6.59/1.54      ( k5_xboole_0(X0,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) = k1_xboole_0 ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3615,plain,
% 6.59/1.54      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.59/1.54      inference(light_normalisation,[status(thm)],[c_3614,c_1]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_14564,plain,
% 6.59/1.54      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 6.59/1.54      inference(demodulation,[status(thm)],[c_3358,c_3615]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_14569,plain,
% 6.59/1.54      ( sK3 = sK2 ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_12421,c_14564]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_6,plain,
% 6.59/1.54      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 6.59/1.54      inference(cnf_transformation,[],[f52]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_3236,plain,
% 6.59/1.54      ( k1_xboole_0 = X0
% 6.59/1.54      | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 6.59/1.54      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_4753,plain,
% 6.59/1.54      ( k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 6.59/1.54      | r1_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 6.59/1.54      inference(superposition,[status(thm)],[c_3805,c_3236]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_14915,plain,
% 6.59/1.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 6.59/1.54      | r1_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 6.59/1.54      inference(demodulation,[status(thm)],[c_14569,c_4753]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(c_14566,plain,
% 6.59/1.54      ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k1_xboole_0 ),
% 6.59/1.54      inference(instantiation,[status(thm)],[c_14564]) ).
% 6.59/1.54  
% 6.59/1.54  cnf(contradiction,plain,
% 6.59/1.54      ( $false ),
% 6.59/1.54      inference(minisat,[status(thm)],[c_14915,c_14566,c_3567,c_1291]) ).
% 6.59/1.54  
% 6.59/1.54  
% 6.59/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 6.59/1.54  
% 6.59/1.54  ------                               Statistics
% 6.59/1.54  
% 6.59/1.54  ------ General
% 6.59/1.54  
% 6.59/1.54  abstr_ref_over_cycles:                  0
% 6.59/1.54  abstr_ref_under_cycles:                 0
% 6.59/1.54  gc_basic_clause_elim:                   0
% 6.59/1.54  forced_gc_time:                         0
% 6.59/1.54  parsing_time:                           0.013
% 6.59/1.54  unif_index_cands_time:                  0.
% 6.59/1.54  unif_index_add_time:                    0.
% 6.59/1.54  orderings_time:                         0.
% 6.59/1.54  out_proof_time:                         0.011
% 6.59/1.54  total_time:                             0.678
% 6.59/1.54  num_of_symbols:                         47
% 6.59/1.54  num_of_terms:                           27777
% 6.59/1.54  
% 6.59/1.54  ------ Preprocessing
% 6.59/1.54  
% 6.59/1.54  num_of_splits:                          0
% 6.59/1.54  num_of_split_atoms:                     0
% 6.59/1.54  num_of_reused_defs:                     0
% 6.59/1.54  num_eq_ax_congr_red:                    28
% 6.59/1.54  num_of_sem_filtered_clauses:            1
% 6.59/1.54  num_of_subtypes:                        0
% 6.59/1.54  monotx_restored_types:                  0
% 6.59/1.54  sat_num_of_epr_types:                   0
% 6.59/1.54  sat_num_of_non_cyclic_types:            0
% 6.59/1.54  sat_guarded_non_collapsed_types:        0
% 6.59/1.54  num_pure_diseq_elim:                    0
% 6.59/1.54  simp_replaced_by:                       0
% 6.59/1.54  res_preprocessed:                       120
% 6.59/1.54  prep_upred:                             0
% 6.59/1.54  prep_unflattend:                        174
% 6.59/1.54  smt_new_axioms:                         0
% 6.59/1.54  pred_elim_cands:                        3
% 6.59/1.54  pred_elim:                              0
% 6.59/1.54  pred_elim_cl:                           0
% 6.59/1.54  pred_elim_cycles:                       3
% 6.59/1.54  merged_defs:                            6
% 6.59/1.54  merged_defs_ncl:                        0
% 6.59/1.54  bin_hyper_res:                          6
% 6.59/1.54  prep_cycles:                            3
% 6.59/1.54  pred_elim_time:                         0.024
% 6.59/1.54  splitting_time:                         0.
% 6.59/1.54  sem_filter_time:                        0.
% 6.59/1.54  monotx_time:                            0.
% 6.59/1.54  subtype_inf_time:                       0.
% 6.59/1.54  
% 6.59/1.54  ------ Problem properties
% 6.59/1.54  
% 6.59/1.54  clauses:                                31
% 6.59/1.54  conjectures:                            2
% 6.59/1.54  epr:                                    7
% 6.59/1.54  horn:                                   27
% 6.59/1.54  ground:                                 2
% 6.59/1.54  unary:                                  10
% 6.59/1.54  binary:                                 13
% 6.59/1.54  lits:                                   70
% 6.59/1.54  lits_eq:                                34
% 6.59/1.54  fd_pure:                                0
% 6.59/1.54  fd_pseudo:                              0
% 6.59/1.54  fd_cond:                                2
% 6.59/1.54  fd_pseudo_cond:                         3
% 6.59/1.54  ac_symbols:                             0
% 6.59/1.54  
% 6.59/1.54  ------ Propositional Solver
% 6.59/1.54  
% 6.59/1.54  prop_solver_calls:                      24
% 6.59/1.54  prop_fast_solver_calls:                 1204
% 6.59/1.54  smt_solver_calls:                       0
% 6.59/1.54  smt_fast_solver_calls:                  0
% 6.59/1.54  prop_num_of_clauses:                    4963
% 6.59/1.54  prop_preprocess_simplified:             16058
% 6.59/1.54  prop_fo_subsumed:                       3
% 6.59/1.54  prop_solver_time:                       0.
% 6.59/1.54  smt_solver_time:                        0.
% 6.59/1.54  smt_fast_solver_time:                   0.
% 6.59/1.54  prop_fast_solver_time:                  0.
% 6.59/1.54  prop_unsat_core_time:                   0.
% 6.59/1.54  
% 6.59/1.54  ------ QBF
% 6.59/1.54  
% 6.59/1.54  qbf_q_res:                              0
% 6.59/1.54  qbf_num_tautologies:                    0
% 6.59/1.54  qbf_prep_cycles:                        0
% 6.59/1.54  
% 6.59/1.54  ------ BMC1
% 6.59/1.54  
% 6.59/1.54  bmc1_current_bound:                     -1
% 6.59/1.54  bmc1_last_solved_bound:                 -1
% 6.59/1.54  bmc1_unsat_core_size:                   -1
% 6.59/1.54  bmc1_unsat_core_parents_size:           -1
% 6.59/1.54  bmc1_merge_next_fun:                    0
% 6.59/1.54  bmc1_unsat_core_clauses_time:           0.
% 6.59/1.54  
% 6.59/1.54  ------ Instantiation
% 6.59/1.54  
% 6.59/1.54  inst_num_of_clauses:                    2055
% 6.59/1.54  inst_num_in_passive:                    1252
% 6.59/1.54  inst_num_in_active:                     347
% 6.59/1.54  inst_num_in_unprocessed:                456
% 6.59/1.54  inst_num_of_loops:                      410
% 6.59/1.54  inst_num_of_learning_restarts:          0
% 6.59/1.54  inst_num_moves_active_passive:          61
% 6.59/1.54  inst_lit_activity:                      0
% 6.59/1.54  inst_lit_activity_moves:                0
% 6.59/1.54  inst_num_tautologies:                   0
% 6.59/1.54  inst_num_prop_implied:                  0
% 6.59/1.54  inst_num_existing_simplified:           0
% 6.59/1.54  inst_num_eq_res_simplified:             0
% 6.59/1.54  inst_num_child_elim:                    0
% 6.59/1.54  inst_num_of_dismatching_blockings:      1395
% 6.59/1.54  inst_num_of_non_proper_insts:           2119
% 6.59/1.54  inst_num_of_duplicates:                 0
% 6.59/1.54  inst_inst_num_from_inst_to_res:         0
% 6.59/1.54  inst_dismatching_checking_time:         0.
% 6.59/1.54  
% 6.59/1.54  ------ Resolution
% 6.59/1.54  
% 6.59/1.54  res_num_of_clauses:                     0
% 6.59/1.54  res_num_in_passive:                     0
% 6.59/1.54  res_num_in_active:                      0
% 6.59/1.54  res_num_of_loops:                       123
% 6.59/1.54  res_forward_subset_subsumed:            57
% 6.59/1.54  res_backward_subset_subsumed:           0
% 6.59/1.54  res_forward_subsumed:                   0
% 6.59/1.54  res_backward_subsumed:                  0
% 6.59/1.54  res_forward_subsumption_resolution:     0
% 6.59/1.54  res_backward_subsumption_resolution:    0
% 6.59/1.54  res_clause_to_clause_subsumption:       1898
% 6.59/1.54  res_orphan_elimination:                 0
% 6.59/1.54  res_tautology_del:                      204
% 6.59/1.54  res_num_eq_res_simplified:              0
% 6.59/1.54  res_num_sel_changes:                    0
% 6.59/1.54  res_moves_from_active_to_pass:          0
% 6.59/1.54  
% 6.59/1.54  ------ Superposition
% 6.59/1.54  
% 6.59/1.54  sup_time_total:                         0.
% 6.59/1.54  sup_time_generating:                    0.
% 6.59/1.54  sup_time_sim_full:                      0.
% 6.59/1.54  sup_time_sim_immed:                     0.
% 6.59/1.54  
% 6.59/1.54  sup_num_of_clauses:                     139
% 6.59/1.54  sup_num_in_active:                      38
% 6.59/1.54  sup_num_in_passive:                     101
% 6.59/1.54  sup_num_of_loops:                       80
% 6.59/1.54  sup_fw_superposition:                   440
% 6.59/1.54  sup_bw_superposition:                   175
% 6.59/1.54  sup_immediate_simplified:               92
% 6.59/1.54  sup_given_eliminated:                   0
% 6.59/1.54  comparisons_done:                       0
% 6.59/1.54  comparisons_avoided:                    65
% 6.59/1.54  
% 6.59/1.54  ------ Simplifications
% 6.59/1.54  
% 6.59/1.54  
% 6.59/1.54  sim_fw_subset_subsumed:                 18
% 6.59/1.54  sim_bw_subset_subsumed:                 33
% 6.59/1.54  sim_fw_subsumed:                        21
% 6.59/1.54  sim_bw_subsumed:                        8
% 6.59/1.54  sim_fw_subsumption_res:                 0
% 6.59/1.54  sim_bw_subsumption_res:                 0
% 6.59/1.54  sim_tautology_del:                      1
% 6.59/1.54  sim_eq_tautology_del:                   37
% 6.59/1.54  sim_eq_res_simp:                        0
% 6.59/1.54  sim_fw_demodulated:                     33
% 6.59/1.54  sim_bw_demodulated:                     38
% 6.59/1.54  sim_light_normalised:                   44
% 6.59/1.54  sim_joinable_taut:                      0
% 6.59/1.54  sim_joinable_simp:                      0
% 6.59/1.54  sim_ac_normalised:                      0
% 6.59/1.54  sim_smt_subsumption:                    0
% 6.59/1.54  
%------------------------------------------------------------------------------
