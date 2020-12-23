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
% DateTime   : Thu Dec  3 11:57:49 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 812 expanded)
%              Number of clauses        :   42 (  91 expanded)
%              Number of leaves         :   19 ( 255 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 (1280 expanded)
%              Number of equality atoms :  238 (1133 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f102,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f91])).

fof(f103,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f102])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK2(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f34])).

fof(f68,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f74])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) = k2_enumset1(X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f62,f75,f77,f77,f77])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1)))) != X0 ) ),
    inference(definition_unfolding,[],[f63,f75,f77])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f61,f75,f77,f77,f77])).

fof(f109,plain,(
    ! [X1] : k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) != k2_enumset1(X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f96])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f74])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f85,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f47,f76])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f48,f75,f76])).

fof(f16,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f17])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f37,f36])).

fof(f71,plain,(
    k4_tarski(sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK2(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,
    ( k2_mcart_1(sK3) = sK3
    | k1_mcart_1(sK3) = sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK2(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_676,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_25,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_668,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( X0 = X1
    | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)))) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))) != X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_671,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1)))) != X0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2630,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_671])).

cnf(c_2647,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | sK2(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_668,c_2630])).

cnf(c_18,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_6,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_785,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(demodulation,[status(thm)],[c_18,c_6])).

cnf(c_7,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1124,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_1125,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1124,c_6])).

cnf(c_1891,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_785,c_1125])).

cnf(c_5388,plain,
    ( sK2(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2647,c_1891])).

cnf(c_27,negated_conjecture,
    ( k4_tarski(sK4,sK5) = sK3 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X0,X2) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_669,plain,
    ( k4_tarski(X0,X1) != sK2(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_863,plain,
    ( sK2(X0) != sK3
    | k1_xboole_0 = X0
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_669])).

cnf(c_5396,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | sK3 != X0
    | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5388,c_863])).

cnf(c_7147,plain,
    ( sK3 != X0
    | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5396,c_1891])).

cnf(c_26,negated_conjecture,
    ( k1_mcart_1(sK3) = sK3
    | k2_mcart_1(sK3) = sK3 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_22,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_878,plain,
    ( k1_mcart_1(sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_27,c_22])).

cnf(c_1399,plain,
    ( k2_mcart_1(sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_26,c_878])).

cnf(c_21,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_876,plain,
    ( k2_mcart_1(sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_27,c_21])).

cnf(c_1401,plain,
    ( sK5 = sK3
    | sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_1399,c_876])).

cnf(c_2007,plain,
    ( k4_tarski(sK4,sK3) = sK3
    | sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_1401,c_27])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X2,X0) != sK2(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_670,plain,
    ( k4_tarski(X0,X1) != sK2(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2010,plain,
    ( sK2(X0) != sK3
    | sK4 = sK3
    | k1_xboole_0 = X0
    | r2_hidden(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_670])).

cnf(c_5393,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
    | sK4 = sK3
    | sK3 != X0
    | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5388,c_2010])).

cnf(c_5825,plain,
    ( sK4 = sK3
    | sK3 != X0
    | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5393,c_1891])).

cnf(c_5834,plain,
    ( sK4 = sK3
    | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5825,c_2630])).

cnf(c_5838,plain,
    ( sK4 = sK3 ),
    inference(superposition,[status(thm)],[c_676,c_5834])).

cnf(c_7153,plain,
    ( sK3 != X0
    | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7147,c_5838])).

cnf(c_7156,plain,
    ( r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7153,c_2630])).

cnf(c_7160,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_676,c_7156])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:25:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.59/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.01  
% 3.59/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/1.01  
% 3.59/1.01  ------  iProver source info
% 3.59/1.01  
% 3.59/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.59/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/1.01  git: non_committed_changes: false
% 3.59/1.01  git: last_make_outside_of_git: false
% 3.59/1.01  
% 3.59/1.01  ------ 
% 3.59/1.01  
% 3.59/1.01  ------ Input Options
% 3.59/1.01  
% 3.59/1.01  --out_options                           all
% 3.59/1.01  --tptp_safe_out                         true
% 3.59/1.01  --problem_path                          ""
% 3.59/1.01  --include_path                          ""
% 3.59/1.01  --clausifier                            res/vclausify_rel
% 3.59/1.01  --clausifier_options                    --mode clausify
% 3.59/1.01  --stdin                                 false
% 3.59/1.01  --stats_out                             sel
% 3.59/1.01  
% 3.59/1.01  ------ General Options
% 3.59/1.01  
% 3.59/1.01  --fof                                   false
% 3.59/1.01  --time_out_real                         604.98
% 3.59/1.01  --time_out_virtual                      -1.
% 3.59/1.01  --symbol_type_check                     false
% 3.59/1.01  --clausify_out                          false
% 3.59/1.01  --sig_cnt_out                           false
% 3.59/1.01  --trig_cnt_out                          false
% 3.59/1.01  --trig_cnt_out_tolerance                1.
% 3.59/1.01  --trig_cnt_out_sk_spl                   false
% 3.59/1.01  --abstr_cl_out                          false
% 3.59/1.01  
% 3.59/1.01  ------ Global Options
% 3.59/1.01  
% 3.59/1.01  --schedule                              none
% 3.59/1.01  --add_important_lit                     false
% 3.59/1.01  --prop_solver_per_cl                    1000
% 3.59/1.01  --min_unsat_core                        false
% 3.59/1.01  --soft_assumptions                      false
% 3.59/1.01  --soft_lemma_size                       3
% 3.59/1.01  --prop_impl_unit_size                   0
% 3.59/1.01  --prop_impl_unit                        []
% 3.59/1.01  --share_sel_clauses                     true
% 3.59/1.01  --reset_solvers                         false
% 3.59/1.01  --bc_imp_inh                            [conj_cone]
% 3.59/1.01  --conj_cone_tolerance                   3.
% 3.59/1.01  --extra_neg_conj                        none
% 3.59/1.01  --large_theory_mode                     true
% 3.59/1.01  --prolific_symb_bound                   200
% 3.59/1.01  --lt_threshold                          2000
% 3.59/1.01  --clause_weak_htbl                      true
% 3.59/1.01  --gc_record_bc_elim                     false
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing Options
% 3.59/1.01  
% 3.59/1.01  --preprocessing_flag                    true
% 3.59/1.01  --time_out_prep_mult                    0.1
% 3.59/1.01  --splitting_mode                        input
% 3.59/1.01  --splitting_grd                         true
% 3.59/1.01  --splitting_cvd                         false
% 3.59/1.01  --splitting_cvd_svl                     false
% 3.59/1.01  --splitting_nvd                         32
% 3.59/1.01  --sub_typing                            true
% 3.59/1.01  --prep_gs_sim                           false
% 3.59/1.01  --prep_unflatten                        true
% 3.59/1.01  --prep_res_sim                          true
% 3.59/1.01  --prep_upred                            true
% 3.59/1.01  --prep_sem_filter                       exhaustive
% 3.59/1.01  --prep_sem_filter_out                   false
% 3.59/1.01  --pred_elim                             false
% 3.59/1.01  --res_sim_input                         true
% 3.59/1.01  --eq_ax_congr_red                       true
% 3.59/1.01  --pure_diseq_elim                       true
% 3.59/1.01  --brand_transform                       false
% 3.59/1.01  --non_eq_to_eq                          false
% 3.59/1.01  --prep_def_merge                        true
% 3.59/1.01  --prep_def_merge_prop_impl              false
% 3.59/1.01  --prep_def_merge_mbd                    true
% 3.59/1.01  --prep_def_merge_tr_red                 false
% 3.59/1.01  --prep_def_merge_tr_cl                  false
% 3.59/1.01  --smt_preprocessing                     true
% 3.59/1.01  --smt_ac_axioms                         fast
% 3.59/1.01  --preprocessed_out                      false
% 3.59/1.01  --preprocessed_stats                    false
% 3.59/1.01  
% 3.59/1.01  ------ Abstraction refinement Options
% 3.59/1.01  
% 3.59/1.01  --abstr_ref                             []
% 3.59/1.01  --abstr_ref_prep                        false
% 3.59/1.01  --abstr_ref_until_sat                   false
% 3.59/1.01  --abstr_ref_sig_restrict                funpre
% 3.59/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.01  --abstr_ref_under                       []
% 3.59/1.01  
% 3.59/1.01  ------ SAT Options
% 3.59/1.01  
% 3.59/1.01  --sat_mode                              false
% 3.59/1.01  --sat_fm_restart_options                ""
% 3.59/1.01  --sat_gr_def                            false
% 3.59/1.01  --sat_epr_types                         true
% 3.59/1.01  --sat_non_cyclic_types                  false
% 3.59/1.01  --sat_finite_models                     false
% 3.59/1.01  --sat_fm_lemmas                         false
% 3.59/1.01  --sat_fm_prep                           false
% 3.59/1.01  --sat_fm_uc_incr                        true
% 3.59/1.01  --sat_out_model                         small
% 3.59/1.01  --sat_out_clauses                       false
% 3.59/1.01  
% 3.59/1.01  ------ QBF Options
% 3.59/1.01  
% 3.59/1.01  --qbf_mode                              false
% 3.59/1.01  --qbf_elim_univ                         false
% 3.59/1.01  --qbf_dom_inst                          none
% 3.59/1.01  --qbf_dom_pre_inst                      false
% 3.59/1.01  --qbf_sk_in                             false
% 3.59/1.01  --qbf_pred_elim                         true
% 3.59/1.01  --qbf_split                             512
% 3.59/1.01  
% 3.59/1.01  ------ BMC1 Options
% 3.59/1.01  
% 3.59/1.01  --bmc1_incremental                      false
% 3.59/1.01  --bmc1_axioms                           reachable_all
% 3.59/1.01  --bmc1_min_bound                        0
% 3.59/1.01  --bmc1_max_bound                        -1
% 3.59/1.01  --bmc1_max_bound_default                -1
% 3.59/1.01  --bmc1_symbol_reachability              true
% 3.59/1.01  --bmc1_property_lemmas                  false
% 3.59/1.01  --bmc1_k_induction                      false
% 3.59/1.01  --bmc1_non_equiv_states                 false
% 3.59/1.01  --bmc1_deadlock                         false
% 3.59/1.01  --bmc1_ucm                              false
% 3.59/1.01  --bmc1_add_unsat_core                   none
% 3.59/1.01  --bmc1_unsat_core_children              false
% 3.59/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.01  --bmc1_out_stat                         full
% 3.59/1.01  --bmc1_ground_init                      false
% 3.59/1.01  --bmc1_pre_inst_next_state              false
% 3.59/1.01  --bmc1_pre_inst_state                   false
% 3.59/1.01  --bmc1_pre_inst_reach_state             false
% 3.59/1.01  --bmc1_out_unsat_core                   false
% 3.59/1.01  --bmc1_aig_witness_out                  false
% 3.59/1.01  --bmc1_verbose                          false
% 3.59/1.01  --bmc1_dump_clauses_tptp                false
% 3.59/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.01  --bmc1_dump_file                        -
% 3.59/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.01  --bmc1_ucm_extend_mode                  1
% 3.59/1.01  --bmc1_ucm_init_mode                    2
% 3.59/1.01  --bmc1_ucm_cone_mode                    none
% 3.59/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.01  --bmc1_ucm_relax_model                  4
% 3.59/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.01  --bmc1_ucm_layered_model                none
% 3.59/1.01  --bmc1_ucm_max_lemma_size               10
% 3.59/1.01  
% 3.59/1.01  ------ AIG Options
% 3.59/1.01  
% 3.59/1.01  --aig_mode                              false
% 3.59/1.01  
% 3.59/1.01  ------ Instantiation Options
% 3.59/1.01  
% 3.59/1.01  --instantiation_flag                    true
% 3.59/1.01  --inst_sos_flag                         false
% 3.59/1.01  --inst_sos_phase                        true
% 3.59/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.01  --inst_lit_sel_side                     num_symb
% 3.59/1.01  --inst_solver_per_active                1400
% 3.59/1.01  --inst_solver_calls_frac                1.
% 3.59/1.01  --inst_passive_queue_type               priority_queues
% 3.59/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.01  --inst_passive_queues_freq              [25;2]
% 3.59/1.01  --inst_dismatching                      true
% 3.59/1.01  --inst_eager_unprocessed_to_passive     true
% 3.59/1.01  --inst_prop_sim_given                   true
% 3.59/1.01  --inst_prop_sim_new                     false
% 3.59/1.01  --inst_subs_new                         false
% 3.59/1.01  --inst_eq_res_simp                      false
% 3.59/1.01  --inst_subs_given                       false
% 3.59/1.01  --inst_orphan_elimination               true
% 3.59/1.01  --inst_learning_loop_flag               true
% 3.59/1.01  --inst_learning_start                   3000
% 3.59/1.01  --inst_learning_factor                  2
% 3.59/1.01  --inst_start_prop_sim_after_learn       3
% 3.59/1.01  --inst_sel_renew                        solver
% 3.59/1.01  --inst_lit_activity_flag                true
% 3.59/1.01  --inst_restr_to_given                   false
% 3.59/1.01  --inst_activity_threshold               500
% 3.59/1.01  --inst_out_proof                        true
% 3.59/1.01  
% 3.59/1.01  ------ Resolution Options
% 3.59/1.01  
% 3.59/1.01  --resolution_flag                       true
% 3.59/1.01  --res_lit_sel                           adaptive
% 3.59/1.01  --res_lit_sel_side                      none
% 3.59/1.01  --res_ordering                          kbo
% 3.59/1.01  --res_to_prop_solver                    active
% 3.59/1.01  --res_prop_simpl_new                    false
% 3.59/1.01  --res_prop_simpl_given                  true
% 3.59/1.01  --res_passive_queue_type                priority_queues
% 3.59/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.01  --res_passive_queues_freq               [15;5]
% 3.59/1.01  --res_forward_subs                      full
% 3.59/1.01  --res_backward_subs                     full
% 3.59/1.01  --res_forward_subs_resolution           true
% 3.59/1.01  --res_backward_subs_resolution          true
% 3.59/1.01  --res_orphan_elimination                true
% 3.59/1.01  --res_time_limit                        2.
% 3.59/1.01  --res_out_proof                         true
% 3.59/1.01  
% 3.59/1.01  ------ Superposition Options
% 3.59/1.01  
% 3.59/1.01  --superposition_flag                    true
% 3.59/1.01  --sup_passive_queue_type                priority_queues
% 3.59/1.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.01  --sup_passive_queues_freq               [1;4]
% 3.59/1.01  --demod_completeness_check              fast
% 3.59/1.01  --demod_use_ground                      true
% 3.59/1.01  --sup_to_prop_solver                    passive
% 3.59/1.01  --sup_prop_simpl_new                    true
% 3.59/1.01  --sup_prop_simpl_given                  true
% 3.59/1.01  --sup_fun_splitting                     false
% 3.59/1.01  --sup_smt_interval                      50000
% 3.59/1.01  
% 3.59/1.01  ------ Superposition Simplification Setup
% 3.59/1.01  
% 3.59/1.01  --sup_indices_passive                   []
% 3.59/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.01  --sup_full_bw                           [BwDemod]
% 3.59/1.01  --sup_immed_triv                        [TrivRules]
% 3.59/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.01  --sup_immed_bw_main                     []
% 3.59/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.01  
% 3.59/1.01  ------ Combination Options
% 3.59/1.01  
% 3.59/1.01  --comb_res_mult                         3
% 3.59/1.01  --comb_sup_mult                         2
% 3.59/1.01  --comb_inst_mult                        10
% 3.59/1.01  
% 3.59/1.01  ------ Debug Options
% 3.59/1.01  
% 3.59/1.01  --dbg_backtrace                         false
% 3.59/1.01  --dbg_dump_prop_clauses                 false
% 3.59/1.01  --dbg_dump_prop_clauses_file            -
% 3.59/1.01  --dbg_out_stat                          false
% 3.59/1.01  ------ Parsing...
% 3.59/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/1.01  ------ Proving...
% 3.59/1.01  ------ Problem Properties 
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  clauses                                 28
% 3.59/1.01  conjectures                             2
% 3.59/1.01  EPR                                     0
% 3.59/1.01  Horn                                    18
% 3.59/1.01  unary                                   10
% 3.59/1.01  binary                                  7
% 3.59/1.01  lits                                    61
% 3.59/1.01  lits eq                                 34
% 3.59/1.01  fd_pure                                 0
% 3.59/1.01  fd_pseudo                               0
% 3.59/1.01  fd_cond                                 3
% 3.59/1.01  fd_pseudo_cond                          8
% 3.59/1.01  AC symbols                              0
% 3.59/1.01  
% 3.59/1.01  ------ Input Options Time Limit: Unbounded
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  ------ 
% 3.59/1.01  Current options:
% 3.59/1.01  ------ 
% 3.59/1.01  
% 3.59/1.01  ------ Input Options
% 3.59/1.01  
% 3.59/1.01  --out_options                           all
% 3.59/1.01  --tptp_safe_out                         true
% 3.59/1.01  --problem_path                          ""
% 3.59/1.01  --include_path                          ""
% 3.59/1.01  --clausifier                            res/vclausify_rel
% 3.59/1.01  --clausifier_options                    --mode clausify
% 3.59/1.01  --stdin                                 false
% 3.59/1.01  --stats_out                             sel
% 3.59/1.01  
% 3.59/1.01  ------ General Options
% 3.59/1.01  
% 3.59/1.01  --fof                                   false
% 3.59/1.01  --time_out_real                         604.98
% 3.59/1.01  --time_out_virtual                      -1.
% 3.59/1.01  --symbol_type_check                     false
% 3.59/1.01  --clausify_out                          false
% 3.59/1.01  --sig_cnt_out                           false
% 3.59/1.01  --trig_cnt_out                          false
% 3.59/1.01  --trig_cnt_out_tolerance                1.
% 3.59/1.01  --trig_cnt_out_sk_spl                   false
% 3.59/1.01  --abstr_cl_out                          false
% 3.59/1.01  
% 3.59/1.01  ------ Global Options
% 3.59/1.01  
% 3.59/1.01  --schedule                              none
% 3.59/1.01  --add_important_lit                     false
% 3.59/1.01  --prop_solver_per_cl                    1000
% 3.59/1.01  --min_unsat_core                        false
% 3.59/1.01  --soft_assumptions                      false
% 3.59/1.01  --soft_lemma_size                       3
% 3.59/1.01  --prop_impl_unit_size                   0
% 3.59/1.01  --prop_impl_unit                        []
% 3.59/1.01  --share_sel_clauses                     true
% 3.59/1.01  --reset_solvers                         false
% 3.59/1.01  --bc_imp_inh                            [conj_cone]
% 3.59/1.01  --conj_cone_tolerance                   3.
% 3.59/1.01  --extra_neg_conj                        none
% 3.59/1.01  --large_theory_mode                     true
% 3.59/1.01  --prolific_symb_bound                   200
% 3.59/1.01  --lt_threshold                          2000
% 3.59/1.01  --clause_weak_htbl                      true
% 3.59/1.01  --gc_record_bc_elim                     false
% 3.59/1.01  
% 3.59/1.01  ------ Preprocessing Options
% 3.59/1.01  
% 3.59/1.01  --preprocessing_flag                    true
% 3.59/1.01  --time_out_prep_mult                    0.1
% 3.59/1.01  --splitting_mode                        input
% 3.59/1.01  --splitting_grd                         true
% 3.59/1.01  --splitting_cvd                         false
% 3.59/1.01  --splitting_cvd_svl                     false
% 3.59/1.01  --splitting_nvd                         32
% 3.59/1.01  --sub_typing                            true
% 3.59/1.01  --prep_gs_sim                           false
% 3.59/1.01  --prep_unflatten                        true
% 3.59/1.01  --prep_res_sim                          true
% 3.59/1.01  --prep_upred                            true
% 3.59/1.01  --prep_sem_filter                       exhaustive
% 3.59/1.01  --prep_sem_filter_out                   false
% 3.59/1.01  --pred_elim                             false
% 3.59/1.01  --res_sim_input                         true
% 3.59/1.01  --eq_ax_congr_red                       true
% 3.59/1.01  --pure_diseq_elim                       true
% 3.59/1.01  --brand_transform                       false
% 3.59/1.01  --non_eq_to_eq                          false
% 3.59/1.01  --prep_def_merge                        true
% 3.59/1.01  --prep_def_merge_prop_impl              false
% 3.59/1.01  --prep_def_merge_mbd                    true
% 3.59/1.01  --prep_def_merge_tr_red                 false
% 3.59/1.01  --prep_def_merge_tr_cl                  false
% 3.59/1.01  --smt_preprocessing                     true
% 3.59/1.01  --smt_ac_axioms                         fast
% 3.59/1.01  --preprocessed_out                      false
% 3.59/1.01  --preprocessed_stats                    false
% 3.59/1.01  
% 3.59/1.01  ------ Abstraction refinement Options
% 3.59/1.01  
% 3.59/1.01  --abstr_ref                             []
% 3.59/1.01  --abstr_ref_prep                        false
% 3.59/1.01  --abstr_ref_until_sat                   false
% 3.59/1.01  --abstr_ref_sig_restrict                funpre
% 3.59/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/1.01  --abstr_ref_under                       []
% 3.59/1.01  
% 3.59/1.01  ------ SAT Options
% 3.59/1.01  
% 3.59/1.01  --sat_mode                              false
% 3.59/1.01  --sat_fm_restart_options                ""
% 3.59/1.01  --sat_gr_def                            false
% 3.59/1.01  --sat_epr_types                         true
% 3.59/1.01  --sat_non_cyclic_types                  false
% 3.59/1.01  --sat_finite_models                     false
% 3.59/1.01  --sat_fm_lemmas                         false
% 3.59/1.01  --sat_fm_prep                           false
% 3.59/1.01  --sat_fm_uc_incr                        true
% 3.59/1.01  --sat_out_model                         small
% 3.59/1.01  --sat_out_clauses                       false
% 3.59/1.01  
% 3.59/1.01  ------ QBF Options
% 3.59/1.01  
% 3.59/1.01  --qbf_mode                              false
% 3.59/1.01  --qbf_elim_univ                         false
% 3.59/1.01  --qbf_dom_inst                          none
% 3.59/1.01  --qbf_dom_pre_inst                      false
% 3.59/1.01  --qbf_sk_in                             false
% 3.59/1.01  --qbf_pred_elim                         true
% 3.59/1.01  --qbf_split                             512
% 3.59/1.01  
% 3.59/1.01  ------ BMC1 Options
% 3.59/1.01  
% 3.59/1.01  --bmc1_incremental                      false
% 3.59/1.01  --bmc1_axioms                           reachable_all
% 3.59/1.01  --bmc1_min_bound                        0
% 3.59/1.01  --bmc1_max_bound                        -1
% 3.59/1.01  --bmc1_max_bound_default                -1
% 3.59/1.01  --bmc1_symbol_reachability              true
% 3.59/1.01  --bmc1_property_lemmas                  false
% 3.59/1.01  --bmc1_k_induction                      false
% 3.59/1.01  --bmc1_non_equiv_states                 false
% 3.59/1.01  --bmc1_deadlock                         false
% 3.59/1.01  --bmc1_ucm                              false
% 3.59/1.01  --bmc1_add_unsat_core                   none
% 3.59/1.01  --bmc1_unsat_core_children              false
% 3.59/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/1.01  --bmc1_out_stat                         full
% 3.59/1.01  --bmc1_ground_init                      false
% 3.59/1.01  --bmc1_pre_inst_next_state              false
% 3.59/1.01  --bmc1_pre_inst_state                   false
% 3.59/1.01  --bmc1_pre_inst_reach_state             false
% 3.59/1.01  --bmc1_out_unsat_core                   false
% 3.59/1.01  --bmc1_aig_witness_out                  false
% 3.59/1.01  --bmc1_verbose                          false
% 3.59/1.01  --bmc1_dump_clauses_tptp                false
% 3.59/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.59/1.01  --bmc1_dump_file                        -
% 3.59/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.59/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.59/1.01  --bmc1_ucm_extend_mode                  1
% 3.59/1.01  --bmc1_ucm_init_mode                    2
% 3.59/1.01  --bmc1_ucm_cone_mode                    none
% 3.59/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.59/1.01  --bmc1_ucm_relax_model                  4
% 3.59/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.59/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/1.01  --bmc1_ucm_layered_model                none
% 3.59/1.01  --bmc1_ucm_max_lemma_size               10
% 3.59/1.01  
% 3.59/1.01  ------ AIG Options
% 3.59/1.01  
% 3.59/1.01  --aig_mode                              false
% 3.59/1.01  
% 3.59/1.01  ------ Instantiation Options
% 3.59/1.01  
% 3.59/1.01  --instantiation_flag                    true
% 3.59/1.01  --inst_sos_flag                         false
% 3.59/1.01  --inst_sos_phase                        true
% 3.59/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/1.01  --inst_lit_sel_side                     num_symb
% 3.59/1.01  --inst_solver_per_active                1400
% 3.59/1.01  --inst_solver_calls_frac                1.
% 3.59/1.01  --inst_passive_queue_type               priority_queues
% 3.59/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/1.01  --inst_passive_queues_freq              [25;2]
% 3.59/1.01  --inst_dismatching                      true
% 3.59/1.01  --inst_eager_unprocessed_to_passive     true
% 3.59/1.01  --inst_prop_sim_given                   true
% 3.59/1.01  --inst_prop_sim_new                     false
% 3.59/1.01  --inst_subs_new                         false
% 3.59/1.01  --inst_eq_res_simp                      false
% 3.59/1.01  --inst_subs_given                       false
% 3.59/1.01  --inst_orphan_elimination               true
% 3.59/1.01  --inst_learning_loop_flag               true
% 3.59/1.01  --inst_learning_start                   3000
% 3.59/1.01  --inst_learning_factor                  2
% 3.59/1.01  --inst_start_prop_sim_after_learn       3
% 3.59/1.01  --inst_sel_renew                        solver
% 3.59/1.01  --inst_lit_activity_flag                true
% 3.59/1.01  --inst_restr_to_given                   false
% 3.59/1.01  --inst_activity_threshold               500
% 3.59/1.01  --inst_out_proof                        true
% 3.59/1.01  
% 3.59/1.01  ------ Resolution Options
% 3.59/1.01  
% 3.59/1.01  --resolution_flag                       true
% 3.59/1.01  --res_lit_sel                           adaptive
% 3.59/1.01  --res_lit_sel_side                      none
% 3.59/1.01  --res_ordering                          kbo
% 3.59/1.01  --res_to_prop_solver                    active
% 3.59/1.01  --res_prop_simpl_new                    false
% 3.59/1.01  --res_prop_simpl_given                  true
% 3.59/1.01  --res_passive_queue_type                priority_queues
% 3.59/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/1.01  --res_passive_queues_freq               [15;5]
% 3.59/1.01  --res_forward_subs                      full
% 3.59/1.01  --res_backward_subs                     full
% 3.59/1.01  --res_forward_subs_resolution           true
% 3.59/1.01  --res_backward_subs_resolution          true
% 3.59/1.01  --res_orphan_elimination                true
% 3.59/1.01  --res_time_limit                        2.
% 3.59/1.01  --res_out_proof                         true
% 3.59/1.01  
% 3.59/1.01  ------ Superposition Options
% 3.59/1.01  
% 3.59/1.01  --superposition_flag                    true
% 3.59/1.01  --sup_passive_queue_type                priority_queues
% 3.59/1.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/1.01  --sup_passive_queues_freq               [1;4]
% 3.59/1.01  --demod_completeness_check              fast
% 3.59/1.01  --demod_use_ground                      true
% 3.59/1.01  --sup_to_prop_solver                    passive
% 3.59/1.01  --sup_prop_simpl_new                    true
% 3.59/1.01  --sup_prop_simpl_given                  true
% 3.59/1.01  --sup_fun_splitting                     false
% 3.59/1.01  --sup_smt_interval                      50000
% 3.59/1.01  
% 3.59/1.01  ------ Superposition Simplification Setup
% 3.59/1.01  
% 3.59/1.01  --sup_indices_passive                   []
% 3.59/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.01  --sup_full_bw                           [BwDemod]
% 3.59/1.01  --sup_immed_triv                        [TrivRules]
% 3.59/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.01  --sup_immed_bw_main                     []
% 3.59/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/1.01  
% 3.59/1.01  ------ Combination Options
% 3.59/1.01  
% 3.59/1.01  --comb_res_mult                         3
% 3.59/1.01  --comb_sup_mult                         2
% 3.59/1.01  --comb_inst_mult                        10
% 3.59/1.01  
% 3.59/1.01  ------ Debug Options
% 3.59/1.01  
% 3.59/1.01  --dbg_backtrace                         false
% 3.59/1.01  --dbg_dump_prop_clauses                 false
% 3.59/1.01  --dbg_dump_prop_clauses_file            -
% 3.59/1.01  --dbg_out_stat                          false
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  ------ Proving...
% 3.59/1.01  
% 3.59/1.01  
% 3.59/1.01  % SZS status Theorem for theBenchmark.p
% 3.59/1.01  
% 3.59/1.01   Resolution empty clause
% 3.59/1.01  
% 3.59/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/1.01  
% 3.59/1.01  fof(f6,axiom,(
% 3.59/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f19,plain,(
% 3.59/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.59/1.01    inference(ennf_transformation,[],[f6])).
% 3.59/1.01  
% 3.59/1.01  fof(f27,plain,(
% 3.59/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.59/1.01    inference(nnf_transformation,[],[f19])).
% 3.59/1.01  
% 3.59/1.01  fof(f28,plain,(
% 3.59/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.59/1.01    inference(flattening,[],[f27])).
% 3.59/1.01  
% 3.59/1.01  fof(f29,plain,(
% 3.59/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.59/1.01    inference(rectify,[],[f28])).
% 3.59/1.01  
% 3.59/1.01  fof(f30,plain,(
% 3.59/1.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.59/1.01    introduced(choice_axiom,[])).
% 3.59/1.01  
% 3.59/1.01  fof(f31,plain,(
% 3.59/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.59/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 3.59/1.01  
% 3.59/1.01  fof(f52,plain,(
% 3.59/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.59/1.01    inference(cnf_transformation,[],[f31])).
% 3.59/1.01  
% 3.59/1.01  fof(f9,axiom,(
% 3.59/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f59,plain,(
% 3.59/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f9])).
% 3.59/1.01  
% 3.59/1.01  fof(f91,plain,(
% 3.59/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.59/1.01    inference(definition_unfolding,[],[f52,f59])).
% 3.59/1.01  
% 3.59/1.01  fof(f102,plain,(
% 3.59/1.01    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 3.59/1.01    inference(equality_resolution,[],[f91])).
% 3.59/1.01  
% 3.59/1.01  fof(f103,plain,(
% 3.59/1.01    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 3.59/1.01    inference(equality_resolution,[],[f102])).
% 3.59/1.01  
% 3.59/1.01  fof(f15,axiom,(
% 3.59/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f20,plain,(
% 3.59/1.01    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.59/1.01    inference(ennf_transformation,[],[f15])).
% 3.59/1.01  
% 3.59/1.01  fof(f34,plain,(
% 3.59/1.01    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)))),
% 3.59/1.01    introduced(choice_axiom,[])).
% 3.59/1.01  
% 3.59/1.01  fof(f35,plain,(
% 3.59/1.01    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK2(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 3.59/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f34])).
% 3.59/1.01  
% 3.59/1.01  fof(f68,plain,(
% 3.59/1.01    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f35])).
% 3.59/1.01  
% 3.59/1.01  fof(f11,axiom,(
% 3.59/1.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f32,plain,(
% 3.59/1.01    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 3.59/1.01    inference(nnf_transformation,[],[f11])).
% 3.59/1.01  
% 3.59/1.01  fof(f62,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 3.59/1.01    inference(cnf_transformation,[],[f32])).
% 3.59/1.01  
% 3.59/1.01  fof(f3,axiom,(
% 3.59/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f46,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.59/1.01    inference(cnf_transformation,[],[f3])).
% 3.59/1.01  
% 3.59/1.01  fof(f13,axiom,(
% 3.59/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f65,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.59/1.01    inference(cnf_transformation,[],[f13])).
% 3.59/1.01  
% 3.59/1.01  fof(f74,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 3.59/1.01    inference(definition_unfolding,[],[f65,f73])).
% 3.59/1.01  
% 3.59/1.01  fof(f75,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.59/1.01    inference(definition_unfolding,[],[f46,f74])).
% 3.59/1.01  
% 3.59/1.01  fof(f7,axiom,(
% 3.59/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f57,plain,(
% 3.59/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f7])).
% 3.59/1.01  
% 3.59/1.01  fof(f8,axiom,(
% 3.59/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f58,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f8])).
% 3.59/1.01  
% 3.59/1.01  fof(f73,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f58,f59])).
% 3.59/1.01  
% 3.59/1.01  fof(f77,plain,(
% 3.59/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f57,f73])).
% 3.59/1.01  
% 3.59/1.01  fof(f95,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) = k2_enumset1(X0,X0,X0,X0) | X0 = X1) )),
% 3.59/1.01    inference(definition_unfolding,[],[f62,f75,f77,f77,f77])).
% 3.59/1.01  
% 3.59/1.01  fof(f12,axiom,(
% 3.59/1.01    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f33,plain,(
% 3.59/1.01    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.59/1.01    inference(nnf_transformation,[],[f12])).
% 3.59/1.01  
% 3.59/1.01  fof(f63,plain,(
% 3.59/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f33])).
% 3.59/1.01  
% 3.59/1.01  fof(f98,plain,(
% 3.59/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1)))) != X0) )),
% 3.59/1.01    inference(definition_unfolding,[],[f63,f75,f77])).
% 3.59/1.01  
% 3.59/1.01  fof(f61,plain,(
% 3.59/1.01    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 3.59/1.01    inference(cnf_transformation,[],[f32])).
% 3.59/1.01  
% 3.59/1.01  fof(f96,plain,(
% 3.59/1.01    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) != k2_enumset1(X0,X0,X0,X0)) )),
% 3.59/1.01    inference(definition_unfolding,[],[f61,f75,f77,f77,f77])).
% 3.59/1.01  
% 3.59/1.01  fof(f109,plain,(
% 3.59/1.01    ( ! [X1] : (k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) != k2_enumset1(X1,X1,X1,X1)) )),
% 3.59/1.01    inference(equality_resolution,[],[f96])).
% 3.59/1.01  
% 3.59/1.01  fof(f2,axiom,(
% 3.59/1.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f18,plain,(
% 3.59/1.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.59/1.01    inference(rectify,[],[f2])).
% 3.59/1.01  
% 3.59/1.01  fof(f45,plain,(
% 3.59/1.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f18])).
% 3.59/1.01  
% 3.59/1.01  fof(f84,plain,(
% 3.59/1.01    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 3.59/1.01    inference(definition_unfolding,[],[f45,f74])).
% 3.59/1.01  
% 3.59/1.01  fof(f4,axiom,(
% 3.59/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f47,plain,(
% 3.59/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f4])).
% 3.59/1.01  
% 3.59/1.01  fof(f10,axiom,(
% 3.59/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f60,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.59/1.01    inference(cnf_transformation,[],[f10])).
% 3.59/1.01  
% 3.59/1.01  fof(f76,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.59/1.01    inference(definition_unfolding,[],[f60,f73])).
% 3.59/1.01  
% 3.59/1.01  fof(f85,plain,(
% 3.59/1.01    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 3.59/1.01    inference(definition_unfolding,[],[f47,f76])).
% 3.59/1.01  
% 3.59/1.01  fof(f5,axiom,(
% 3.59/1.01    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f48,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f5])).
% 3.59/1.01  
% 3.59/1.01  fof(f86,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) = k1_xboole_0) )),
% 3.59/1.01    inference(definition_unfolding,[],[f48,f75,f76])).
% 3.59/1.01  
% 3.59/1.01  fof(f16,conjecture,(
% 3.59/1.01    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f17,negated_conjecture,(
% 3.59/1.01    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.59/1.01    inference(negated_conjecture,[],[f16])).
% 3.59/1.01  
% 3.59/1.01  fof(f21,plain,(
% 3.59/1.01    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 3.59/1.01    inference(ennf_transformation,[],[f17])).
% 3.59/1.01  
% 3.59/1.01  fof(f37,plain,(
% 3.59/1.01    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK4,sK5) = X0) )),
% 3.59/1.01    introduced(choice_axiom,[])).
% 3.59/1.01  
% 3.59/1.01  fof(f36,plain,(
% 3.59/1.01    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3) & ? [X2,X1] : k4_tarski(X1,X2) = sK3)),
% 3.59/1.01    introduced(choice_axiom,[])).
% 3.59/1.01  
% 3.59/1.01  fof(f38,plain,(
% 3.59/1.01    (k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3) & k4_tarski(sK4,sK5) = sK3),
% 3.59/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f37,f36])).
% 3.59/1.01  
% 3.59/1.01  fof(f71,plain,(
% 3.59/1.01    k4_tarski(sK4,sK5) = sK3),
% 3.59/1.01    inference(cnf_transformation,[],[f38])).
% 3.59/1.01  
% 3.59/1.01  fof(f69,plain,(
% 3.59/1.01    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK2(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f35])).
% 3.59/1.01  
% 3.59/1.01  fof(f72,plain,(
% 3.59/1.01    k2_mcart_1(sK3) = sK3 | k1_mcart_1(sK3) = sK3),
% 3.59/1.01    inference(cnf_transformation,[],[f38])).
% 3.59/1.01  
% 3.59/1.01  fof(f14,axiom,(
% 3.59/1.01    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.59/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/1.01  
% 3.59/1.01  fof(f66,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f14])).
% 3.59/1.01  
% 3.59/1.01  fof(f67,plain,(
% 3.59/1.01    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.59/1.01    inference(cnf_transformation,[],[f14])).
% 3.59/1.01  
% 3.59/1.01  fof(f70,plain,(
% 3.59/1.01    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK2(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.59/1.01    inference(cnf_transformation,[],[f35])).
% 3.59/1.01  
% 3.59/1.01  cnf(c_13,plain,
% 3.59/1.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 3.59/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_676,plain,
% 3.59/1.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_25,plain,
% 3.59/1.01      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.59/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_668,plain,
% 3.59/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_17,plain,
% 3.59/1.01      ( X0 = X1
% 3.59/1.01      | k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)))) = k2_enumset1(X1,X1,X1,X1) ),
% 3.59/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_20,plain,
% 3.59/1.01      ( ~ r2_hidden(X0,X1)
% 3.59/1.01      | k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X0,X0,X0,X0)))) != X1 ),
% 3.59/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_671,plain,
% 3.59/1.01      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1)))) != X0
% 3.59/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 3.59/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2630,plain,
% 3.59/1.01      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_17,c_671]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_2647,plain,
% 3.59/1.01      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.59/1.01      | sK2(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.59/1.01      inference(superposition,[status(thm)],[c_668,c_2630]) ).
% 3.59/1.01  
% 3.59/1.01  cnf(c_18,plain,
% 3.59/1.01      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)))) != k2_enumset1(X0,X0,X0,X0) ),
% 3.59/1.02      inference(cnf_transformation,[],[f109]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_6,plain,
% 3.59/1.02      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.59/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_785,plain,
% 3.59/1.02      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 3.59/1.02      inference(demodulation,[status(thm)],[c_18,c_6]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_7,plain,
% 3.59/1.02      ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
% 3.59/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_8,plain,
% 3.59/1.02      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) = k1_xboole_0 ),
% 3.59/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_1124,plain,
% 3.59/1.02      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0 ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_1125,plain,
% 3.59/1.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.59/1.02      inference(light_normalisation,[status(thm)],[c_1124,c_6]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_1891,plain,
% 3.59/1.02      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 3.59/1.02      inference(demodulation,[status(thm)],[c_785,c_1125]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_5388,plain,
% 3.59/1.02      ( sK2(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.59/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2647,c_1891]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_27,negated_conjecture,
% 3.59/1.02      ( k4_tarski(sK4,sK5) = sK3 ),
% 3.59/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_24,plain,
% 3.59/1.02      ( ~ r2_hidden(X0,X1) | k4_tarski(X0,X2) != sK2(X1) | k1_xboole_0 = X1 ),
% 3.59/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_669,plain,
% 3.59/1.02      ( k4_tarski(X0,X1) != sK2(X2)
% 3.59/1.02      | k1_xboole_0 = X2
% 3.59/1.02      | r2_hidden(X0,X2) != iProver_top ),
% 3.59/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_863,plain,
% 3.59/1.02      ( sK2(X0) != sK3 | k1_xboole_0 = X0 | r2_hidden(sK4,X0) != iProver_top ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_27,c_669]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_5396,plain,
% 3.59/1.02      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.59/1.02      | sK3 != X0
% 3.59/1.02      | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_5388,c_863]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_7147,plain,
% 3.59/1.02      ( sK3 != X0 | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.59/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5396,c_1891]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_26,negated_conjecture,
% 3.59/1.02      ( k1_mcart_1(sK3) = sK3 | k2_mcart_1(sK3) = sK3 ),
% 3.59/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_22,plain,
% 3.59/1.02      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.59/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_878,plain,
% 3.59/1.02      ( k1_mcart_1(sK3) = sK4 ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_27,c_22]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_1399,plain,
% 3.59/1.02      ( k2_mcart_1(sK3) = sK3 | sK4 = sK3 ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_26,c_878]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_21,plain,
% 3.59/1.02      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.59/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_876,plain,
% 3.59/1.02      ( k2_mcart_1(sK3) = sK5 ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_27,c_21]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_1401,plain,
% 3.59/1.02      ( sK5 = sK3 | sK4 = sK3 ),
% 3.59/1.02      inference(demodulation,[status(thm)],[c_1399,c_876]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_2007,plain,
% 3.59/1.02      ( k4_tarski(sK4,sK3) = sK3 | sK4 = sK3 ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_1401,c_27]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_23,plain,
% 3.59/1.02      ( ~ r2_hidden(X0,X1) | k4_tarski(X2,X0) != sK2(X1) | k1_xboole_0 = X1 ),
% 3.59/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_670,plain,
% 3.59/1.02      ( k4_tarski(X0,X1) != sK2(X2)
% 3.59/1.02      | k1_xboole_0 = X2
% 3.59/1.02      | r2_hidden(X1,X2) != iProver_top ),
% 3.59/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_2010,plain,
% 3.59/1.02      ( sK2(X0) != sK3
% 3.59/1.02      | sK4 = sK3
% 3.59/1.02      | k1_xboole_0 = X0
% 3.59/1.02      | r2_hidden(sK3,X0) != iProver_top ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_2007,c_670]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_5393,plain,
% 3.59/1.02      ( k2_enumset1(X0,X0,X0,X0) = k1_xboole_0
% 3.59/1.02      | sK4 = sK3
% 3.59/1.02      | sK3 != X0
% 3.59/1.02      | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_5388,c_2010]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_5825,plain,
% 3.59/1.02      ( sK4 = sK3
% 3.59/1.02      | sK3 != X0
% 3.59/1.02      | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.59/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5393,c_1891]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_5834,plain,
% 3.59/1.02      ( sK4 = sK3 | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.59/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_5825,c_2630]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_5838,plain,
% 3.59/1.02      ( sK4 = sK3 ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_676,c_5834]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_7153,plain,
% 3.59/1.02      ( sK3 != X0 | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.59/1.02      inference(light_normalisation,[status(thm)],[c_7147,c_5838]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_7156,plain,
% 3.59/1.02      ( r2_hidden(sK3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.59/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_7153,c_2630]) ).
% 3.59/1.02  
% 3.59/1.02  cnf(c_7160,plain,
% 3.59/1.02      ( $false ),
% 3.59/1.02      inference(superposition,[status(thm)],[c_676,c_7156]) ).
% 3.59/1.02  
% 3.59/1.02  
% 3.59/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/1.02  
% 3.59/1.02  ------                               Statistics
% 3.59/1.02  
% 3.59/1.02  ------ Selected
% 3.59/1.02  
% 3.59/1.02  total_time:                             0.3
% 3.59/1.02  
%------------------------------------------------------------------------------
