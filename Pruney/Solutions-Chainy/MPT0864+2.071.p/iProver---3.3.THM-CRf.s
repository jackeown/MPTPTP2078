%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:59 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  129 (1060 expanded)
%              Number of clauses        :   49 (  91 expanded)
%              Number of leaves         :   23 ( 344 expanded)
%              Depth                    :   17
%              Number of atoms          :  326 (1631 expanded)
%              Number of equality atoms :  234 (1444 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f22,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK4,sK5) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK3) = sK3
        | k1_mcart_1(sK3) = sK3 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK3 ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k2_mcart_1(sK3) = sK3
      | k1_mcart_1(sK3) = sK3 )
    & k4_tarski(sK4,sK5) = sK3 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f37,f36])).

fof(f76,plain,
    ( k2_mcart_1(sK3) = sK3
    | k1_mcart_1(sK3) = sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    k4_tarski(sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f81])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f77])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f78])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f80])).

fof(f91,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f55,f81,f84,f81])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f90,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f56,f81,f81,f84])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f81])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f82])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f54,f83,f84,f84,f84])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f23])).

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

fof(f62,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f62])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(nnf_transformation,[],[f24])).

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
     => ( ( ~ sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f21,f24,f23])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f70])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f53,f83,f84,f84,f84])).

fof(f92,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f82,f84,f81,f84])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f84])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_27,negated_conjecture,
    ( k1_mcart_1(sK3) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( k4_tarski(sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1735,plain,
    ( k1_mcart_1(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_28,c_26])).

cnf(c_1766,plain,
    ( k2_mcart_1(sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_27,c_1735])).

cnf(c_25,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1707,plain,
    ( k2_mcart_1(sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_28,c_25])).

cnf(c_1768,plain,
    ( sK5 = sK3
    | sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_1766,c_1707])).

cnf(c_1771,plain,
    ( k4_tarski(sK4,sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1768,c_28])).

cnf(c_9,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2087,plain,
    ( k6_enumset1(k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),sK3) = k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1771,c_9])).

cnf(c_2086,plain,
    ( k6_enumset1(k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),sK3) = k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) ),
    inference(superposition,[status(thm)],[c_28,c_9])).

cnf(c_3632,plain,
    ( k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5))
    | sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_2087,c_2086])).

cnf(c_8,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2248,plain,
    ( k4_tarski(X0,X1) = X2
    | k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k1_setfam_1(k6_enumset1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_6468,plain,
    ( k4_tarski(sK4,sK5) = X0
    | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK3))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_3632,c_2248])).

cnf(c_2084,plain,
    ( k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_28,c_9])).

cnf(c_6502,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(sK4,sK3))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | sK4 = sK3
    | sK3 = X0 ),
    inference(demodulation,[status(thm)],[c_6468,c_28,c_2084])).

cnf(c_21,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_40,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_42,plain,
    ( sP0(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_418,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | r2_hidden(X0,X9)
    | X10 != X1
    | X11 != X2
    | X12 != X3
    | X13 != X4
    | X14 != X5
    | X15 != X6
    | X16 != X7
    | X17 != X8
    | k6_enumset1(X17,X16,X15,X14,X13,X12,X11,X10) != X9 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_419,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_420,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_422,plain,
    ( sP0(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != iProver_top
    | r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_7,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1638,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7,c_0,c_5])).

cnf(c_1657,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2677,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2678,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) != iProver_top
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2677])).

cnf(c_2680,plain,
    ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2678])).

cnf(c_1897,plain,
    ( k6_enumset1(k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),sK3) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(superposition,[status(thm)],[c_28,c_8])).

cnf(c_2388,plain,
    ( k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_28,c_1897])).

cnf(c_2479,plain,
    ( k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1768,c_2388])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1537,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6862,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | sK4 = sK3
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2479,c_1537])).

cnf(c_7512,plain,
    ( sK4 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6502,c_42,c_422,c_1657,c_2680,c_6862])).

cnf(c_7535,plain,
    ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_7512,c_2388])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1536,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7732,plain,
    ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
    | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7535,c_1536])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7732,c_2680,c_1657,c_422,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.86/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/1.01  
% 3.86/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/1.01  
% 3.86/1.01  ------  iProver source info
% 3.86/1.01  
% 3.86/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.86/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/1.01  git: non_committed_changes: false
% 3.86/1.01  git: last_make_outside_of_git: false
% 3.86/1.01  
% 3.86/1.01  ------ 
% 3.86/1.01  ------ Parsing...
% 3.86/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/1.01  
% 3.86/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.86/1.01  
% 3.86/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/1.01  
% 3.86/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/1.01  ------ Proving...
% 3.86/1.01  ------ Problem Properties 
% 3.86/1.01  
% 3.86/1.01  
% 3.86/1.01  clauses                                 29
% 3.86/1.01  conjectures                             2
% 3.86/1.01  EPR                                     11
% 3.86/1.01  Horn                                    25
% 3.86/1.01  unary                                   17
% 3.86/1.01  binary                                  7
% 3.86/1.01  lits                                    52
% 3.86/1.01  lits eq                                 23
% 3.86/1.01  fd_pure                                 0
% 3.86/1.01  fd_pseudo                               0
% 3.86/1.01  fd_cond                                 2
% 3.86/1.01  fd_pseudo_cond                          3
% 3.86/1.01  AC symbols                              0
% 3.86/1.01  
% 3.86/1.01  ------ Input Options Time Limit: Unbounded
% 3.86/1.01  
% 3.86/1.01  
% 3.86/1.01  ------ 
% 3.86/1.01  Current options:
% 3.86/1.01  ------ 
% 3.86/1.01  
% 3.86/1.01  
% 3.86/1.01  
% 3.86/1.01  
% 3.86/1.01  ------ Proving...
% 3.86/1.01  
% 3.86/1.01  
% 3.86/1.01  % SZS status Theorem for theBenchmark.p
% 3.86/1.01  
% 3.86/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/1.01  
% 3.86/1.01  fof(f18,conjecture,(
% 3.86/1.01    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f19,negated_conjecture,(
% 3.86/1.01    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.86/1.01    inference(negated_conjecture,[],[f18])).
% 3.86/1.01  
% 3.86/1.01  fof(f22,plain,(
% 3.86/1.01    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 3.86/1.01    inference(ennf_transformation,[],[f19])).
% 3.86/1.01  
% 3.86/1.01  fof(f37,plain,(
% 3.86/1.01    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK4,sK5) = X0) )),
% 3.86/1.01    introduced(choice_axiom,[])).
% 3.86/1.01  
% 3.86/1.01  fof(f36,plain,(
% 3.86/1.01    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3) & ? [X2,X1] : k4_tarski(X1,X2) = sK3)),
% 3.86/1.01    introduced(choice_axiom,[])).
% 3.86/1.01  
% 3.86/1.01  fof(f38,plain,(
% 3.86/1.01    (k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3) & k4_tarski(sK4,sK5) = sK3),
% 3.86/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f37,f36])).
% 3.86/1.01  
% 3.86/1.01  fof(f76,plain,(
% 3.86/1.01    k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3),
% 3.86/1.01    inference(cnf_transformation,[],[f38])).
% 3.86/1.01  
% 3.86/1.01  fof(f75,plain,(
% 3.86/1.01    k4_tarski(sK4,sK5) = sK3),
% 3.86/1.01    inference(cnf_transformation,[],[f38])).
% 3.86/1.01  
% 3.86/1.01  fof(f17,axiom,(
% 3.86/1.01    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f73,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.86/1.01    inference(cnf_transformation,[],[f17])).
% 3.86/1.01  
% 3.86/1.01  fof(f74,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.86/1.01    inference(cnf_transformation,[],[f17])).
% 3.86/1.01  
% 3.86/1.01  fof(f14,axiom,(
% 3.86/1.01    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f55,plain,(
% 3.86/1.01    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 3.86/1.01    inference(cnf_transformation,[],[f14])).
% 3.86/1.01  
% 3.86/1.01  fof(f3,axiom,(
% 3.86/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f41,plain,(
% 3.86/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f3])).
% 3.86/1.01  
% 3.86/1.01  fof(f84,plain,(
% 3.86/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.86/1.01    inference(definition_unfolding,[],[f41,f81])).
% 3.86/1.01  
% 3.86/1.01  fof(f4,axiom,(
% 3.86/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f42,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f4])).
% 3.86/1.01  
% 3.86/1.01  fof(f5,axiom,(
% 3.86/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f43,plain,(
% 3.86/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f5])).
% 3.86/1.01  
% 3.86/1.01  fof(f6,axiom,(
% 3.86/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f44,plain,(
% 3.86/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f6])).
% 3.86/1.01  
% 3.86/1.01  fof(f7,axiom,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f45,plain,(
% 3.86/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f7])).
% 3.86/1.01  
% 3.86/1.01  fof(f8,axiom,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f46,plain,(
% 3.86/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f8])).
% 3.86/1.01  
% 3.86/1.01  fof(f9,axiom,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f47,plain,(
% 3.86/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f9])).
% 3.86/1.01  
% 3.86/1.01  fof(f77,plain,(
% 3.86/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.86/1.01    inference(definition_unfolding,[],[f46,f47])).
% 3.86/1.01  
% 3.86/1.01  fof(f78,plain,(
% 3.86/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.86/1.01    inference(definition_unfolding,[],[f45,f77])).
% 3.86/1.01  
% 3.86/1.01  fof(f79,plain,(
% 3.86/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.86/1.01    inference(definition_unfolding,[],[f44,f78])).
% 3.86/1.01  
% 3.86/1.01  fof(f80,plain,(
% 3.86/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.86/1.01    inference(definition_unfolding,[],[f43,f79])).
% 3.86/1.01  
% 3.86/1.01  fof(f81,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.86/1.01    inference(definition_unfolding,[],[f42,f80])).
% 3.86/1.01  
% 3.86/1.01  fof(f91,plain,(
% 3.86/1.01    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.86/1.01    inference(definition_unfolding,[],[f55,f81,f84,f81])).
% 3.86/1.01  
% 3.86/1.01  fof(f56,plain,(
% 3.86/1.01    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 3.86/1.01    inference(cnf_transformation,[],[f14])).
% 3.86/1.01  
% 3.86/1.01  fof(f90,plain,(
% 3.86/1.01    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 3.86/1.01    inference(definition_unfolding,[],[f56,f81,f81,f84])).
% 3.86/1.01  
% 3.86/1.01  fof(f13,axiom,(
% 3.86/1.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f27,plain,(
% 3.86/1.01    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.86/1.01    inference(nnf_transformation,[],[f13])).
% 3.86/1.01  
% 3.86/1.01  fof(f54,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.86/1.01    inference(cnf_transformation,[],[f27])).
% 3.86/1.01  
% 3.86/1.01  fof(f1,axiom,(
% 3.86/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f39,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.86/1.01    inference(cnf_transformation,[],[f1])).
% 3.86/1.01  
% 3.86/1.01  fof(f16,axiom,(
% 3.86/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f72,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.86/1.01    inference(cnf_transformation,[],[f16])).
% 3.86/1.01  
% 3.86/1.01  fof(f82,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.86/1.01    inference(definition_unfolding,[],[f72,f81])).
% 3.86/1.01  
% 3.86/1.01  fof(f83,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.86/1.01    inference(definition_unfolding,[],[f39,f82])).
% 3.86/1.01  
% 3.86/1.01  fof(f88,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 3.86/1.01    inference(definition_unfolding,[],[f54,f83,f84,f84,f84])).
% 3.86/1.01  
% 3.86/1.01  fof(f23,plain,(
% 3.86/1.01    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 3.86/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.86/1.01  
% 3.86/1.01  fof(f32,plain,(
% 3.86/1.01    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.86/1.01    inference(nnf_transformation,[],[f23])).
% 3.86/1.01  
% 3.86/1.01  fof(f33,plain,(
% 3.86/1.01    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.86/1.01    inference(flattening,[],[f32])).
% 3.86/1.01  
% 3.86/1.01  fof(f34,plain,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.86/1.01    inference(rectify,[],[f33])).
% 3.86/1.01  
% 3.86/1.01  fof(f62,plain,(
% 3.86/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 3.86/1.01    inference(cnf_transformation,[],[f34])).
% 3.86/1.01  
% 3.86/1.01  fof(f100,plain,(
% 3.86/1.01    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.86/1.01    inference(equality_resolution,[],[f62])).
% 3.86/1.01  
% 3.86/1.01  fof(f24,plain,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.86/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.86/1.01  
% 3.86/1.01  fof(f28,plain,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.86/1.01    inference(nnf_transformation,[],[f24])).
% 3.86/1.01  
% 3.86/1.01  fof(f29,plain,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.86/1.01    inference(rectify,[],[f28])).
% 3.86/1.01  
% 3.86/1.01  fof(f30,plain,(
% 3.86/1.01    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 3.86/1.01    introduced(choice_axiom,[])).
% 3.86/1.01  
% 3.86/1.01  fof(f31,plain,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.86/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 3.86/1.01  
% 3.86/1.01  fof(f58,plain,(
% 3.86/1.01    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f31])).
% 3.86/1.01  
% 3.86/1.01  fof(f15,axiom,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f21,plain,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 3.86/1.01    inference(ennf_transformation,[],[f15])).
% 3.86/1.01  
% 3.86/1.01  fof(f25,plain,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 3.86/1.01    inference(definition_folding,[],[f21,f24,f23])).
% 3.86/1.01  
% 3.86/1.01  fof(f35,plain,(
% 3.86/1.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 3.86/1.01    inference(nnf_transformation,[],[f25])).
% 3.86/1.01  
% 3.86/1.01  fof(f70,plain,(
% 3.86/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 3.86/1.01    inference(cnf_transformation,[],[f35])).
% 3.86/1.01  
% 3.86/1.01  fof(f101,plain,(
% 3.86/1.01    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 3.86/1.01    inference(equality_resolution,[],[f70])).
% 3.86/1.01  
% 3.86/1.01  fof(f53,plain,(
% 3.86/1.01    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f27])).
% 3.86/1.01  
% 3.86/1.01  fof(f89,plain,(
% 3.86/1.01    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.86/1.01    inference(definition_unfolding,[],[f53,f83,f84,f84,f84])).
% 3.86/1.01  
% 3.86/1.01  fof(f92,plain,(
% 3.86/1.01    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 3.86/1.01    inference(equality_resolution,[],[f89])).
% 3.86/1.01  
% 3.86/1.01  fof(f2,axiom,(
% 3.86/1.01    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f40,plain,(
% 3.86/1.01    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.86/1.01    inference(cnf_transformation,[],[f2])).
% 3.86/1.01  
% 3.86/1.01  fof(f12,axiom,(
% 3.86/1.01    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f52,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f12])).
% 3.86/1.01  
% 3.86/1.01  fof(f87,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.86/1.01    inference(definition_unfolding,[],[f52,f82,f84,f81,f84])).
% 3.86/1.01  
% 3.86/1.01  fof(f10,axiom,(
% 3.86/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f26,plain,(
% 3.86/1.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.86/1.01    inference(nnf_transformation,[],[f10])).
% 3.86/1.01  
% 3.86/1.01  fof(f49,plain,(
% 3.86/1.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.86/1.01    inference(cnf_transformation,[],[f26])).
% 3.86/1.01  
% 3.86/1.01  fof(f85,plain,(
% 3.86/1.01    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.86/1.01    inference(definition_unfolding,[],[f49,f84])).
% 3.86/1.01  
% 3.86/1.01  fof(f11,axiom,(
% 3.86/1.01    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 3.86/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/1.01  
% 3.86/1.01  fof(f20,plain,(
% 3.86/1.01    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 3.86/1.01    inference(ennf_transformation,[],[f11])).
% 3.86/1.01  
% 3.86/1.01  fof(f51,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 3.86/1.01    inference(cnf_transformation,[],[f20])).
% 3.86/1.01  
% 3.86/1.01  fof(f50,plain,(
% 3.86/1.01    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 3.86/1.01    inference(cnf_transformation,[],[f20])).
% 3.86/1.01  
% 3.86/1.01  cnf(c_27,negated_conjecture,
% 3.86/1.01      ( k1_mcart_1(sK3) = sK3 | k2_mcart_1(sK3) = sK3 ),
% 3.86/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_28,negated_conjecture,
% 3.86/1.01      ( k4_tarski(sK4,sK5) = sK3 ),
% 3.86/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_26,plain,
% 3.86/1.01      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.86/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1735,plain,
% 3.86/1.01      ( k1_mcart_1(sK3) = sK4 ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_28,c_26]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1766,plain,
% 3.86/1.01      ( k2_mcart_1(sK3) = sK3 | sK4 = sK3 ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_27,c_1735]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_25,plain,
% 3.86/1.01      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.86/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1707,plain,
% 3.86/1.01      ( k2_mcart_1(sK3) = sK5 ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_28,c_25]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1768,plain,
% 3.86/1.01      ( sK5 = sK3 | sK4 = sK3 ),
% 3.86/1.01      inference(demodulation,[status(thm)],[c_1766,c_1707]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1771,plain,
% 3.86/1.01      ( k4_tarski(sK4,sK3) = sK3 | sK4 = sK3 ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_1768,c_28]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_9,plain,
% 3.86/1.01      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 3.86/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_2087,plain,
% 3.86/1.01      ( k6_enumset1(k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),sK3) = k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))
% 3.86/1.01      | sK4 = sK3 ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_1771,c_9]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_2086,plain,
% 3.86/1.01      ( k6_enumset1(k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),k4_tarski(sK4,X0),sK3) = k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5)) ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_28,c_9]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_3632,plain,
% 3.86/1.01      ( k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)) = k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK5))
% 3.86/1.01      | sK4 = sK3 ),
% 3.86/1.01      inference(demodulation,[status(thm)],[c_2087,c_2086]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_8,plain,
% 3.86/1.01      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 3.86/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_6,plain,
% 3.86/1.01      ( X0 = X1
% 3.86/1.01      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 3.86/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_2248,plain,
% 3.86/1.01      ( k4_tarski(X0,X1) = X2
% 3.86/1.01      | k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k1_setfam_1(k6_enumset1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_6468,plain,
% 3.86/1.01      ( k4_tarski(sK4,sK5) = X0
% 3.86/1.01      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK3))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.86/1.01      | sK4 = sK3 ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_3632,c_2248]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_2084,plain,
% 3.86/1.01      ( k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,X0)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(sK4,X0)) ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_28,c_9]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_6502,plain,
% 3.86/1.01      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,k4_tarski(sK4,sK3))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.86/1.01      | sK4 = sK3
% 3.86/1.01      | sK3 = X0 ),
% 3.86/1.01      inference(demodulation,[status(thm)],[c_6468,c_28,c_2084]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_21,plain,
% 3.86/1.01      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 3.86/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_40,plain,
% 3.86/1.01      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) = iProver_top ),
% 3.86/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_42,plain,
% 3.86/1.01      ( sP0(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = iProver_top ),
% 3.86/1.01      inference(instantiation,[status(thm)],[c_40]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_12,plain,
% 3.86/1.01      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.86/1.01      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 3.86/1.01      | r2_hidden(X0,X9) ),
% 3.86/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_24,plain,
% 3.86/1.01      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 3.86/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_418,plain,
% 3.86/1.01      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.86/1.01      | r2_hidden(X0,X9)
% 3.86/1.01      | X10 != X1
% 3.86/1.01      | X11 != X2
% 3.86/1.01      | X12 != X3
% 3.86/1.01      | X13 != X4
% 3.86/1.01      | X14 != X5
% 3.86/1.01      | X15 != X6
% 3.86/1.01      | X16 != X7
% 3.86/1.01      | X17 != X8
% 3.86/1.01      | k6_enumset1(X17,X16,X15,X14,X13,X12,X11,X10) != X9 ),
% 3.86/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_419,plain,
% 3.86/1.01      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.86/1.01      | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) ),
% 3.86/1.01      inference(unflattening,[status(thm)],[c_418]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_420,plain,
% 3.86/1.01      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 3.86/1.01      | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) = iProver_top ),
% 3.86/1.01      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_422,plain,
% 3.86/1.01      ( sP0(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != iProver_top
% 3.86/1.01      | r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.86/1.01      inference(instantiation,[status(thm)],[c_420]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_7,plain,
% 3.86/1.01      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.86/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_0,plain,
% 3.86/1.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.86/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_5,plain,
% 3.86/1.01      ( k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 3.86/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1638,plain,
% 3.86/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 3.86/1.01      inference(demodulation,[status(thm)],[c_7,c_0,c_5]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1657,plain,
% 3.86/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k1_xboole_0 ),
% 3.86/1.01      inference(instantiation,[status(thm)],[c_1638]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1,plain,
% 3.86/1.01      ( ~ r2_hidden(X0,X1)
% 3.86/1.01      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 3.86/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_2677,plain,
% 3.86/1.01      ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 3.86/1.01      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
% 3.86/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_2678,plain,
% 3.86/1.01      ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) != iProver_top
% 3.86/1.01      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) = iProver_top ),
% 3.86/1.01      inference(predicate_to_equality,[status(thm)],[c_2677]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_2680,plain,
% 3.86/1.01      ( r2_hidden(sK3,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 3.86/1.01      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 3.86/1.01      inference(instantiation,[status(thm)],[c_2678]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1897,plain,
% 3.86/1.01      ( k6_enumset1(k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),k4_tarski(X0,sK5),sK3) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_28,c_8]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_2388,plain,
% 3.86/1.01      ( k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_28,c_1897]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_2479,plain,
% 3.86/1.01      ( k2_zfmisc_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)
% 3.86/1.01      | sK4 = sK3 ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_1768,c_2388]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_3,plain,
% 3.86/1.01      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 3.86/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1537,plain,
% 3.86/1.01      ( k1_xboole_0 = X0
% 3.86/1.01      | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 3.86/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_6862,plain,
% 3.86/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 3.86/1.01      | sK4 = sK3
% 3.86/1.01      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_2479,c_1537]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_7512,plain,
% 3.86/1.01      ( sK4 = sK3 ),
% 3.86/1.01      inference(global_propositional_subsumption,
% 3.86/1.01                [status(thm)],
% 3.86/1.01                [c_6502,c_42,c_422,c_1657,c_2680,c_6862]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_7535,plain,
% 3.86/1.01      ( k2_zfmisc_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
% 3.86/1.01      inference(demodulation,[status(thm)],[c_7512,c_2388]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_4,plain,
% 3.86/1.01      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 3.86/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_1536,plain,
% 3.86/1.01      ( k1_xboole_0 = X0
% 3.86/1.01      | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.86/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(c_7732,plain,
% 3.86/1.01      ( k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k1_xboole_0
% 3.86/1.01      | r1_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.86/1.01      inference(superposition,[status(thm)],[c_7535,c_1536]) ).
% 3.86/1.01  
% 3.86/1.01  cnf(contradiction,plain,
% 3.86/1.01      ( $false ),
% 3.86/1.01      inference(minisat,[status(thm)],[c_7732,c_2680,c_1657,c_422,c_42]) ).
% 3.86/1.01  
% 3.86/1.01  
% 3.86/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.86/1.01  
% 3.86/1.01  ------                               Statistics
% 3.86/1.01  
% 3.86/1.01  ------ Selected
% 3.86/1.01  
% 3.86/1.01  total_time:                             0.46
% 3.86/1.01  
%------------------------------------------------------------------------------
