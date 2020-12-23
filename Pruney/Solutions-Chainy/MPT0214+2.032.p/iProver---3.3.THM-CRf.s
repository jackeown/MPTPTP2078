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
% DateTime   : Thu Dec  3 11:28:47 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 791 expanded)
%              Number of clauses        :   33 ( 111 expanded)
%              Number of leaves         :   16 ( 255 expanded)
%              Depth                    :   19
%              Number of atoms          :  255 (1109 expanded)
%              Number of equality atoms :  186 ( 931 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK2 != sK3
      & r1_tarski(k1_tarski(sK2),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK2 != sK3
    & r1_tarski(k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).

fof(f55,plain,(
    r1_tarski(k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f75,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f55,f59,f59])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f57,f51,f59])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f85,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f76,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f77,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f76])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f83,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f72])).

fof(f84,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f83])).

fof(f56,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_159,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | k3_xboole_0(X1,X0) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_160,plain,
    ( k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1881,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK3,sK3,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_160,c_0])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1882,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_1881,c_2,c_3])).

cnf(c_2045,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK2),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK3,sK3,sK3,sK2)))) = k2_enumset1(sK3,sK3,sK3,X0) ),
    inference(superposition,[status(thm)],[c_1882,c_0])).

cnf(c_2061,plain,
    ( k2_enumset1(sK3,sK3,sK2,X0) = k2_enumset1(sK3,sK3,sK3,X0) ),
    inference(demodulation,[status(thm)],[c_2045,c_0])).

cnf(c_2079,plain,
    ( k5_xboole_0(k2_enumset1(sK3,sK3,sK2,X0),k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(sK3,sK3,sK2,X0)))) = k2_enumset1(sK3,sK3,X0,X1) ),
    inference(superposition,[status(thm)],[c_2061,c_0])).

cnf(c_2096,plain,
    ( k2_enumset1(sK3,sK2,X0,X1) = k2_enumset1(sK3,sK3,X0,X1) ),
    inference(demodulation,[status(thm)],[c_2079,c_0])).

cnf(c_2097,plain,
    ( k2_enumset1(sK3,sK2,sK3,X0) = k2_enumset1(sK3,sK3,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_2096,c_2061])).

cnf(c_2109,plain,
    ( k2_enumset1(sK3,sK2,sK2,X0) = k2_enumset1(sK3,sK2,sK3,X0) ),
    inference(demodulation,[status(thm)],[c_2097,c_2096])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1387,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2052,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_1387])).

cnf(c_2361,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK2,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2052,c_2096])).

cnf(c_3022,plain,
    ( sK3 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK2,sK2,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2109,c_2361])).

cnf(c_3037,plain,
    ( sK3 = sK2
    | r2_hidden(sK2,k2_enumset1(sK3,sK2,sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3022])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1394,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2332,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2096,c_1394])).

cnf(c_2379,plain,
    ( r2_hidden(sK2,k2_enumset1(sK3,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2332])).

cnf(c_1193,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1495,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_1496,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_25,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_22,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3037,c_2379,c_1496,c_25,c_22,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.47/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.47/1.02  
% 1.47/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.47/1.02  
% 1.47/1.02  ------  iProver source info
% 1.47/1.02  
% 1.47/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.47/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.47/1.02  git: non_committed_changes: false
% 1.47/1.02  git: last_make_outside_of_git: false
% 1.47/1.02  
% 1.47/1.02  ------ 
% 1.47/1.02  
% 1.47/1.02  ------ Input Options
% 1.47/1.02  
% 1.47/1.02  --out_options                           all
% 1.47/1.02  --tptp_safe_out                         true
% 1.47/1.02  --problem_path                          ""
% 1.47/1.02  --include_path                          ""
% 1.47/1.02  --clausifier                            res/vclausify_rel
% 1.47/1.02  --clausifier_options                    --mode clausify
% 1.47/1.02  --stdin                                 false
% 1.47/1.02  --stats_out                             all
% 1.47/1.02  
% 1.47/1.02  ------ General Options
% 1.47/1.02  
% 1.47/1.02  --fof                                   false
% 1.47/1.02  --time_out_real                         305.
% 1.47/1.02  --time_out_virtual                      -1.
% 1.47/1.02  --symbol_type_check                     false
% 1.47/1.02  --clausify_out                          false
% 1.47/1.02  --sig_cnt_out                           false
% 1.47/1.03  --trig_cnt_out                          false
% 1.47/1.03  --trig_cnt_out_tolerance                1.
% 1.47/1.03  --trig_cnt_out_sk_spl                   false
% 1.47/1.03  --abstr_cl_out                          false
% 1.47/1.03  
% 1.47/1.03  ------ Global Options
% 1.47/1.03  
% 1.47/1.03  --schedule                              default
% 1.47/1.03  --add_important_lit                     false
% 1.47/1.03  --prop_solver_per_cl                    1000
% 1.47/1.03  --min_unsat_core                        false
% 1.47/1.03  --soft_assumptions                      false
% 1.47/1.03  --soft_lemma_size                       3
% 1.47/1.03  --prop_impl_unit_size                   0
% 1.47/1.03  --prop_impl_unit                        []
% 1.47/1.03  --share_sel_clauses                     true
% 1.47/1.03  --reset_solvers                         false
% 1.47/1.03  --bc_imp_inh                            [conj_cone]
% 1.47/1.03  --conj_cone_tolerance                   3.
% 1.47/1.03  --extra_neg_conj                        none
% 1.47/1.03  --large_theory_mode                     true
% 1.47/1.03  --prolific_symb_bound                   200
% 1.47/1.03  --lt_threshold                          2000
% 1.47/1.03  --clause_weak_htbl                      true
% 1.47/1.03  --gc_record_bc_elim                     false
% 1.47/1.03  
% 1.47/1.03  ------ Preprocessing Options
% 1.47/1.03  
% 1.47/1.03  --preprocessing_flag                    true
% 1.47/1.03  --time_out_prep_mult                    0.1
% 1.47/1.03  --splitting_mode                        input
% 1.47/1.03  --splitting_grd                         true
% 1.47/1.03  --splitting_cvd                         false
% 1.47/1.03  --splitting_cvd_svl                     false
% 1.47/1.03  --splitting_nvd                         32
% 1.47/1.03  --sub_typing                            true
% 1.47/1.03  --prep_gs_sim                           true
% 1.47/1.03  --prep_unflatten                        true
% 1.47/1.03  --prep_res_sim                          true
% 1.47/1.03  --prep_upred                            true
% 1.47/1.03  --prep_sem_filter                       exhaustive
% 1.47/1.03  --prep_sem_filter_out                   false
% 1.47/1.03  --pred_elim                             true
% 1.47/1.03  --res_sim_input                         true
% 1.47/1.03  --eq_ax_congr_red                       true
% 1.47/1.03  --pure_diseq_elim                       true
% 1.47/1.03  --brand_transform                       false
% 1.47/1.03  --non_eq_to_eq                          false
% 1.47/1.03  --prep_def_merge                        true
% 1.47/1.03  --prep_def_merge_prop_impl              false
% 1.47/1.03  --prep_def_merge_mbd                    true
% 1.47/1.03  --prep_def_merge_tr_red                 false
% 1.47/1.03  --prep_def_merge_tr_cl                  false
% 1.47/1.03  --smt_preprocessing                     true
% 1.47/1.03  --smt_ac_axioms                         fast
% 1.47/1.03  --preprocessed_out                      false
% 1.47/1.03  --preprocessed_stats                    false
% 1.47/1.03  
% 1.47/1.03  ------ Abstraction refinement Options
% 1.47/1.03  
% 1.47/1.03  --abstr_ref                             []
% 1.47/1.03  --abstr_ref_prep                        false
% 1.47/1.03  --abstr_ref_until_sat                   false
% 1.47/1.03  --abstr_ref_sig_restrict                funpre
% 1.47/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.47/1.03  --abstr_ref_under                       []
% 1.47/1.03  
% 1.47/1.03  ------ SAT Options
% 1.47/1.03  
% 1.47/1.03  --sat_mode                              false
% 1.47/1.03  --sat_fm_restart_options                ""
% 1.47/1.03  --sat_gr_def                            false
% 1.47/1.03  --sat_epr_types                         true
% 1.47/1.03  --sat_non_cyclic_types                  false
% 1.47/1.03  --sat_finite_models                     false
% 1.47/1.03  --sat_fm_lemmas                         false
% 1.47/1.03  --sat_fm_prep                           false
% 1.47/1.03  --sat_fm_uc_incr                        true
% 1.47/1.03  --sat_out_model                         small
% 1.47/1.03  --sat_out_clauses                       false
% 1.47/1.03  
% 1.47/1.03  ------ QBF Options
% 1.47/1.03  
% 1.47/1.03  --qbf_mode                              false
% 1.47/1.03  --qbf_elim_univ                         false
% 1.47/1.03  --qbf_dom_inst                          none
% 1.47/1.03  --qbf_dom_pre_inst                      false
% 1.47/1.03  --qbf_sk_in                             false
% 1.47/1.03  --qbf_pred_elim                         true
% 1.47/1.03  --qbf_split                             512
% 1.47/1.03  
% 1.47/1.03  ------ BMC1 Options
% 1.47/1.03  
% 1.47/1.03  --bmc1_incremental                      false
% 1.47/1.03  --bmc1_axioms                           reachable_all
% 1.47/1.03  --bmc1_min_bound                        0
% 1.47/1.03  --bmc1_max_bound                        -1
% 1.47/1.03  --bmc1_max_bound_default                -1
% 1.47/1.03  --bmc1_symbol_reachability              true
% 1.47/1.03  --bmc1_property_lemmas                  false
% 1.47/1.03  --bmc1_k_induction                      false
% 1.47/1.03  --bmc1_non_equiv_states                 false
% 1.47/1.03  --bmc1_deadlock                         false
% 1.47/1.03  --bmc1_ucm                              false
% 1.47/1.03  --bmc1_add_unsat_core                   none
% 1.47/1.03  --bmc1_unsat_core_children              false
% 1.47/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.47/1.03  --bmc1_out_stat                         full
% 1.47/1.03  --bmc1_ground_init                      false
% 1.47/1.03  --bmc1_pre_inst_next_state              false
% 1.47/1.03  --bmc1_pre_inst_state                   false
% 1.47/1.03  --bmc1_pre_inst_reach_state             false
% 1.47/1.03  --bmc1_out_unsat_core                   false
% 1.47/1.03  --bmc1_aig_witness_out                  false
% 1.47/1.03  --bmc1_verbose                          false
% 1.47/1.03  --bmc1_dump_clauses_tptp                false
% 1.47/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.47/1.03  --bmc1_dump_file                        -
% 1.47/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.47/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.47/1.03  --bmc1_ucm_extend_mode                  1
% 1.47/1.03  --bmc1_ucm_init_mode                    2
% 1.47/1.03  --bmc1_ucm_cone_mode                    none
% 1.47/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.47/1.03  --bmc1_ucm_relax_model                  4
% 1.47/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.47/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.47/1.03  --bmc1_ucm_layered_model                none
% 1.47/1.03  --bmc1_ucm_max_lemma_size               10
% 1.47/1.03  
% 1.47/1.03  ------ AIG Options
% 1.47/1.03  
% 1.47/1.03  --aig_mode                              false
% 1.47/1.03  
% 1.47/1.03  ------ Instantiation Options
% 1.47/1.03  
% 1.47/1.03  --instantiation_flag                    true
% 1.47/1.03  --inst_sos_flag                         false
% 1.47/1.03  --inst_sos_phase                        true
% 1.47/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.47/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.47/1.03  --inst_lit_sel_side                     num_symb
% 1.47/1.03  --inst_solver_per_active                1400
% 1.47/1.03  --inst_solver_calls_frac                1.
% 1.47/1.03  --inst_passive_queue_type               priority_queues
% 1.47/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.47/1.03  --inst_passive_queues_freq              [25;2]
% 1.47/1.03  --inst_dismatching                      true
% 1.47/1.03  --inst_eager_unprocessed_to_passive     true
% 1.47/1.03  --inst_prop_sim_given                   true
% 1.47/1.03  --inst_prop_sim_new                     false
% 1.47/1.03  --inst_subs_new                         false
% 1.47/1.03  --inst_eq_res_simp                      false
% 1.47/1.03  --inst_subs_given                       false
% 1.47/1.03  --inst_orphan_elimination               true
% 1.47/1.03  --inst_learning_loop_flag               true
% 1.47/1.03  --inst_learning_start                   3000
% 1.47/1.03  --inst_learning_factor                  2
% 1.47/1.03  --inst_start_prop_sim_after_learn       3
% 1.47/1.03  --inst_sel_renew                        solver
% 1.47/1.03  --inst_lit_activity_flag                true
% 1.47/1.03  --inst_restr_to_given                   false
% 1.47/1.03  --inst_activity_threshold               500
% 1.47/1.03  --inst_out_proof                        true
% 1.47/1.03  
% 1.47/1.03  ------ Resolution Options
% 1.47/1.03  
% 1.47/1.03  --resolution_flag                       true
% 1.47/1.03  --res_lit_sel                           adaptive
% 1.47/1.03  --res_lit_sel_side                      none
% 1.47/1.03  --res_ordering                          kbo
% 1.47/1.03  --res_to_prop_solver                    active
% 1.47/1.03  --res_prop_simpl_new                    false
% 1.47/1.03  --res_prop_simpl_given                  true
% 1.47/1.03  --res_passive_queue_type                priority_queues
% 1.47/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.47/1.03  --res_passive_queues_freq               [15;5]
% 1.47/1.03  --res_forward_subs                      full
% 1.47/1.03  --res_backward_subs                     full
% 1.47/1.03  --res_forward_subs_resolution           true
% 1.47/1.03  --res_backward_subs_resolution          true
% 1.47/1.03  --res_orphan_elimination                true
% 1.47/1.03  --res_time_limit                        2.
% 1.47/1.03  --res_out_proof                         true
% 1.47/1.03  
% 1.47/1.03  ------ Superposition Options
% 1.47/1.03  
% 1.47/1.03  --superposition_flag                    true
% 1.47/1.03  --sup_passive_queue_type                priority_queues
% 1.47/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.47/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.47/1.03  --demod_completeness_check              fast
% 1.47/1.03  --demod_use_ground                      true
% 1.47/1.03  --sup_to_prop_solver                    passive
% 1.47/1.03  --sup_prop_simpl_new                    true
% 1.47/1.03  --sup_prop_simpl_given                  true
% 1.47/1.03  --sup_fun_splitting                     false
% 1.47/1.03  --sup_smt_interval                      50000
% 1.47/1.03  
% 1.47/1.03  ------ Superposition Simplification Setup
% 1.47/1.03  
% 1.47/1.03  --sup_indices_passive                   []
% 1.47/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.47/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/1.03  --sup_full_bw                           [BwDemod]
% 1.47/1.03  --sup_immed_triv                        [TrivRules]
% 1.47/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.47/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/1.03  --sup_immed_bw_main                     []
% 1.47/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.47/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.47/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.47/1.03  
% 1.47/1.03  ------ Combination Options
% 1.47/1.03  
% 1.47/1.03  --comb_res_mult                         3
% 1.47/1.03  --comb_sup_mult                         2
% 1.47/1.03  --comb_inst_mult                        10
% 1.47/1.03  
% 1.47/1.03  ------ Debug Options
% 1.47/1.03  
% 1.47/1.03  --dbg_backtrace                         false
% 1.47/1.03  --dbg_dump_prop_clauses                 false
% 1.47/1.03  --dbg_dump_prop_clauses_file            -
% 1.47/1.03  --dbg_out_stat                          false
% 1.47/1.03  ------ Parsing...
% 1.47/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.47/1.03  
% 1.47/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.47/1.03  
% 1.47/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.47/1.03  
% 1.47/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.47/1.03  ------ Proving...
% 1.47/1.03  ------ Problem Properties 
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  clauses                                 18
% 1.47/1.03  conjectures                             1
% 1.47/1.03  EPR                                     1
% 1.47/1.03  Horn                                    15
% 1.47/1.03  unary                                   10
% 1.47/1.03  binary                                  1
% 1.47/1.03  lits                                    36
% 1.47/1.03  lits eq                                 24
% 1.47/1.03  fd_pure                                 0
% 1.47/1.03  fd_pseudo                               0
% 1.47/1.03  fd_cond                                 0
% 1.47/1.03  fd_pseudo_cond                          6
% 1.47/1.03  AC symbols                              0
% 1.47/1.03  
% 1.47/1.03  ------ Schedule dynamic 5 is on 
% 1.47/1.03  
% 1.47/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  ------ 
% 1.47/1.03  Current options:
% 1.47/1.03  ------ 
% 1.47/1.03  
% 1.47/1.03  ------ Input Options
% 1.47/1.03  
% 1.47/1.03  --out_options                           all
% 1.47/1.03  --tptp_safe_out                         true
% 1.47/1.03  --problem_path                          ""
% 1.47/1.03  --include_path                          ""
% 1.47/1.03  --clausifier                            res/vclausify_rel
% 1.47/1.03  --clausifier_options                    --mode clausify
% 1.47/1.03  --stdin                                 false
% 1.47/1.03  --stats_out                             all
% 1.47/1.03  
% 1.47/1.03  ------ General Options
% 1.47/1.03  
% 1.47/1.03  --fof                                   false
% 1.47/1.03  --time_out_real                         305.
% 1.47/1.03  --time_out_virtual                      -1.
% 1.47/1.03  --symbol_type_check                     false
% 1.47/1.03  --clausify_out                          false
% 1.47/1.03  --sig_cnt_out                           false
% 1.47/1.03  --trig_cnt_out                          false
% 1.47/1.03  --trig_cnt_out_tolerance                1.
% 1.47/1.03  --trig_cnt_out_sk_spl                   false
% 1.47/1.03  --abstr_cl_out                          false
% 1.47/1.03  
% 1.47/1.03  ------ Global Options
% 1.47/1.03  
% 1.47/1.03  --schedule                              default
% 1.47/1.03  --add_important_lit                     false
% 1.47/1.03  --prop_solver_per_cl                    1000
% 1.47/1.03  --min_unsat_core                        false
% 1.47/1.03  --soft_assumptions                      false
% 1.47/1.03  --soft_lemma_size                       3
% 1.47/1.03  --prop_impl_unit_size                   0
% 1.47/1.03  --prop_impl_unit                        []
% 1.47/1.03  --share_sel_clauses                     true
% 1.47/1.03  --reset_solvers                         false
% 1.47/1.03  --bc_imp_inh                            [conj_cone]
% 1.47/1.03  --conj_cone_tolerance                   3.
% 1.47/1.03  --extra_neg_conj                        none
% 1.47/1.03  --large_theory_mode                     true
% 1.47/1.03  --prolific_symb_bound                   200
% 1.47/1.03  --lt_threshold                          2000
% 1.47/1.03  --clause_weak_htbl                      true
% 1.47/1.03  --gc_record_bc_elim                     false
% 1.47/1.03  
% 1.47/1.03  ------ Preprocessing Options
% 1.47/1.03  
% 1.47/1.03  --preprocessing_flag                    true
% 1.47/1.03  --time_out_prep_mult                    0.1
% 1.47/1.03  --splitting_mode                        input
% 1.47/1.03  --splitting_grd                         true
% 1.47/1.03  --splitting_cvd                         false
% 1.47/1.03  --splitting_cvd_svl                     false
% 1.47/1.03  --splitting_nvd                         32
% 1.47/1.03  --sub_typing                            true
% 1.47/1.03  --prep_gs_sim                           true
% 1.47/1.03  --prep_unflatten                        true
% 1.47/1.03  --prep_res_sim                          true
% 1.47/1.03  --prep_upred                            true
% 1.47/1.03  --prep_sem_filter                       exhaustive
% 1.47/1.03  --prep_sem_filter_out                   false
% 1.47/1.03  --pred_elim                             true
% 1.47/1.03  --res_sim_input                         true
% 1.47/1.03  --eq_ax_congr_red                       true
% 1.47/1.03  --pure_diseq_elim                       true
% 1.47/1.03  --brand_transform                       false
% 1.47/1.03  --non_eq_to_eq                          false
% 1.47/1.03  --prep_def_merge                        true
% 1.47/1.03  --prep_def_merge_prop_impl              false
% 1.47/1.03  --prep_def_merge_mbd                    true
% 1.47/1.03  --prep_def_merge_tr_red                 false
% 1.47/1.03  --prep_def_merge_tr_cl                  false
% 1.47/1.03  --smt_preprocessing                     true
% 1.47/1.03  --smt_ac_axioms                         fast
% 1.47/1.03  --preprocessed_out                      false
% 1.47/1.03  --preprocessed_stats                    false
% 1.47/1.03  
% 1.47/1.03  ------ Abstraction refinement Options
% 1.47/1.03  
% 1.47/1.03  --abstr_ref                             []
% 1.47/1.03  --abstr_ref_prep                        false
% 1.47/1.03  --abstr_ref_until_sat                   false
% 1.47/1.03  --abstr_ref_sig_restrict                funpre
% 1.47/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.47/1.03  --abstr_ref_under                       []
% 1.47/1.03  
% 1.47/1.03  ------ SAT Options
% 1.47/1.03  
% 1.47/1.03  --sat_mode                              false
% 1.47/1.03  --sat_fm_restart_options                ""
% 1.47/1.03  --sat_gr_def                            false
% 1.47/1.03  --sat_epr_types                         true
% 1.47/1.03  --sat_non_cyclic_types                  false
% 1.47/1.03  --sat_finite_models                     false
% 1.47/1.03  --sat_fm_lemmas                         false
% 1.47/1.03  --sat_fm_prep                           false
% 1.47/1.03  --sat_fm_uc_incr                        true
% 1.47/1.03  --sat_out_model                         small
% 1.47/1.03  --sat_out_clauses                       false
% 1.47/1.03  
% 1.47/1.03  ------ QBF Options
% 1.47/1.03  
% 1.47/1.03  --qbf_mode                              false
% 1.47/1.03  --qbf_elim_univ                         false
% 1.47/1.03  --qbf_dom_inst                          none
% 1.47/1.03  --qbf_dom_pre_inst                      false
% 1.47/1.03  --qbf_sk_in                             false
% 1.47/1.03  --qbf_pred_elim                         true
% 1.47/1.03  --qbf_split                             512
% 1.47/1.03  
% 1.47/1.03  ------ BMC1 Options
% 1.47/1.03  
% 1.47/1.03  --bmc1_incremental                      false
% 1.47/1.03  --bmc1_axioms                           reachable_all
% 1.47/1.03  --bmc1_min_bound                        0
% 1.47/1.03  --bmc1_max_bound                        -1
% 1.47/1.03  --bmc1_max_bound_default                -1
% 1.47/1.03  --bmc1_symbol_reachability              true
% 1.47/1.03  --bmc1_property_lemmas                  false
% 1.47/1.03  --bmc1_k_induction                      false
% 1.47/1.03  --bmc1_non_equiv_states                 false
% 1.47/1.03  --bmc1_deadlock                         false
% 1.47/1.03  --bmc1_ucm                              false
% 1.47/1.03  --bmc1_add_unsat_core                   none
% 1.47/1.03  --bmc1_unsat_core_children              false
% 1.47/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.47/1.03  --bmc1_out_stat                         full
% 1.47/1.03  --bmc1_ground_init                      false
% 1.47/1.03  --bmc1_pre_inst_next_state              false
% 1.47/1.03  --bmc1_pre_inst_state                   false
% 1.47/1.03  --bmc1_pre_inst_reach_state             false
% 1.47/1.03  --bmc1_out_unsat_core                   false
% 1.47/1.03  --bmc1_aig_witness_out                  false
% 1.47/1.03  --bmc1_verbose                          false
% 1.47/1.03  --bmc1_dump_clauses_tptp                false
% 1.47/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.47/1.03  --bmc1_dump_file                        -
% 1.47/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.47/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.47/1.03  --bmc1_ucm_extend_mode                  1
% 1.47/1.03  --bmc1_ucm_init_mode                    2
% 1.47/1.03  --bmc1_ucm_cone_mode                    none
% 1.47/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.47/1.03  --bmc1_ucm_relax_model                  4
% 1.47/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.47/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.47/1.03  --bmc1_ucm_layered_model                none
% 1.47/1.03  --bmc1_ucm_max_lemma_size               10
% 1.47/1.03  
% 1.47/1.03  ------ AIG Options
% 1.47/1.03  
% 1.47/1.03  --aig_mode                              false
% 1.47/1.03  
% 1.47/1.03  ------ Instantiation Options
% 1.47/1.03  
% 1.47/1.03  --instantiation_flag                    true
% 1.47/1.03  --inst_sos_flag                         false
% 1.47/1.03  --inst_sos_phase                        true
% 1.47/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.47/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.47/1.03  --inst_lit_sel_side                     none
% 1.47/1.03  --inst_solver_per_active                1400
% 1.47/1.03  --inst_solver_calls_frac                1.
% 1.47/1.03  --inst_passive_queue_type               priority_queues
% 1.47/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.47/1.03  --inst_passive_queues_freq              [25;2]
% 1.47/1.03  --inst_dismatching                      true
% 1.47/1.03  --inst_eager_unprocessed_to_passive     true
% 1.47/1.03  --inst_prop_sim_given                   true
% 1.47/1.03  --inst_prop_sim_new                     false
% 1.47/1.03  --inst_subs_new                         false
% 1.47/1.03  --inst_eq_res_simp                      false
% 1.47/1.03  --inst_subs_given                       false
% 1.47/1.03  --inst_orphan_elimination               true
% 1.47/1.03  --inst_learning_loop_flag               true
% 1.47/1.03  --inst_learning_start                   3000
% 1.47/1.03  --inst_learning_factor                  2
% 1.47/1.03  --inst_start_prop_sim_after_learn       3
% 1.47/1.03  --inst_sel_renew                        solver
% 1.47/1.03  --inst_lit_activity_flag                true
% 1.47/1.03  --inst_restr_to_given                   false
% 1.47/1.03  --inst_activity_threshold               500
% 1.47/1.03  --inst_out_proof                        true
% 1.47/1.03  
% 1.47/1.03  ------ Resolution Options
% 1.47/1.03  
% 1.47/1.03  --resolution_flag                       false
% 1.47/1.03  --res_lit_sel                           adaptive
% 1.47/1.03  --res_lit_sel_side                      none
% 1.47/1.03  --res_ordering                          kbo
% 1.47/1.03  --res_to_prop_solver                    active
% 1.47/1.03  --res_prop_simpl_new                    false
% 1.47/1.03  --res_prop_simpl_given                  true
% 1.47/1.03  --res_passive_queue_type                priority_queues
% 1.47/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.47/1.03  --res_passive_queues_freq               [15;5]
% 1.47/1.03  --res_forward_subs                      full
% 1.47/1.03  --res_backward_subs                     full
% 1.47/1.03  --res_forward_subs_resolution           true
% 1.47/1.03  --res_backward_subs_resolution          true
% 1.47/1.03  --res_orphan_elimination                true
% 1.47/1.03  --res_time_limit                        2.
% 1.47/1.03  --res_out_proof                         true
% 1.47/1.03  
% 1.47/1.03  ------ Superposition Options
% 1.47/1.03  
% 1.47/1.03  --superposition_flag                    true
% 1.47/1.03  --sup_passive_queue_type                priority_queues
% 1.47/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.47/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.47/1.03  --demod_completeness_check              fast
% 1.47/1.03  --demod_use_ground                      true
% 1.47/1.03  --sup_to_prop_solver                    passive
% 1.47/1.03  --sup_prop_simpl_new                    true
% 1.47/1.03  --sup_prop_simpl_given                  true
% 1.47/1.03  --sup_fun_splitting                     false
% 1.47/1.03  --sup_smt_interval                      50000
% 1.47/1.03  
% 1.47/1.03  ------ Superposition Simplification Setup
% 1.47/1.03  
% 1.47/1.03  --sup_indices_passive                   []
% 1.47/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.47/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.47/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/1.03  --sup_full_bw                           [BwDemod]
% 1.47/1.03  --sup_immed_triv                        [TrivRules]
% 1.47/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.47/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/1.03  --sup_immed_bw_main                     []
% 1.47/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.47/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.47/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.47/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.47/1.03  
% 1.47/1.03  ------ Combination Options
% 1.47/1.03  
% 1.47/1.03  --comb_res_mult                         3
% 1.47/1.03  --comb_sup_mult                         2
% 1.47/1.03  --comb_inst_mult                        10
% 1.47/1.03  
% 1.47/1.03  ------ Debug Options
% 1.47/1.03  
% 1.47/1.03  --dbg_backtrace                         false
% 1.47/1.03  --dbg_dump_prop_clauses                 false
% 1.47/1.03  --dbg_dump_prop_clauses_file            -
% 1.47/1.03  --dbg_out_stat                          false
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  ------ Proving...
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  % SZS status Theorem for theBenchmark.p
% 1.47/1.03  
% 1.47/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.47/1.03  
% 1.47/1.03  fof(f2,axiom,(
% 1.47/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f17,plain,(
% 1.47/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.47/1.03    inference(ennf_transformation,[],[f2])).
% 1.47/1.03  
% 1.47/1.03  fof(f32,plain,(
% 1.47/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.47/1.03    inference(cnf_transformation,[],[f17])).
% 1.47/1.03  
% 1.47/1.03  fof(f15,conjecture,(
% 1.47/1.03    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f16,negated_conjecture,(
% 1.47/1.03    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.47/1.03    inference(negated_conjecture,[],[f15])).
% 1.47/1.03  
% 1.47/1.03  fof(f19,plain,(
% 1.47/1.03    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.47/1.03    inference(ennf_transformation,[],[f16])).
% 1.47/1.03  
% 1.47/1.03  fof(f29,plain,(
% 1.47/1.03    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK2 != sK3 & r1_tarski(k1_tarski(sK2),k1_tarski(sK3)))),
% 1.47/1.03    introduced(choice_axiom,[])).
% 1.47/1.03  
% 1.47/1.03  fof(f30,plain,(
% 1.47/1.03    sK2 != sK3 & r1_tarski(k1_tarski(sK2),k1_tarski(sK3))),
% 1.47/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).
% 1.47/1.03  
% 1.47/1.03  fof(f55,plain,(
% 1.47/1.03    r1_tarski(k1_tarski(sK2),k1_tarski(sK3))),
% 1.47/1.03    inference(cnf_transformation,[],[f30])).
% 1.47/1.03  
% 1.47/1.03  fof(f9,axiom,(
% 1.47/1.03    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f49,plain,(
% 1.47/1.03    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.47/1.03    inference(cnf_transformation,[],[f9])).
% 1.47/1.03  
% 1.47/1.03  fof(f10,axiom,(
% 1.47/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f50,plain,(
% 1.47/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/1.03    inference(cnf_transformation,[],[f10])).
% 1.47/1.03  
% 1.47/1.03  fof(f11,axiom,(
% 1.47/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f51,plain,(
% 1.47/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.47/1.03    inference(cnf_transformation,[],[f11])).
% 1.47/1.03  
% 1.47/1.03  fof(f58,plain,(
% 1.47/1.03    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/1.03    inference(definition_unfolding,[],[f50,f51])).
% 1.47/1.03  
% 1.47/1.03  fof(f59,plain,(
% 1.47/1.03    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.47/1.03    inference(definition_unfolding,[],[f49,f58])).
% 1.47/1.03  
% 1.47/1.03  fof(f75,plain,(
% 1.47/1.03    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.47/1.03    inference(definition_unfolding,[],[f55,f59,f59])).
% 1.47/1.03  
% 1.47/1.03  fof(f8,axiom,(
% 1.47/1.03    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f48,plain,(
% 1.47/1.03    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/1.03    inference(cnf_transformation,[],[f8])).
% 1.47/1.03  
% 1.47/1.03  fof(f5,axiom,(
% 1.47/1.03    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f35,plain,(
% 1.47/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.47/1.03    inference(cnf_transformation,[],[f5])).
% 1.47/1.03  
% 1.47/1.03  fof(f1,axiom,(
% 1.47/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f31,plain,(
% 1.47/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.47/1.03    inference(cnf_transformation,[],[f1])).
% 1.47/1.03  
% 1.47/1.03  fof(f57,plain,(
% 1.47/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 1.47/1.03    inference(definition_unfolding,[],[f35,f31])).
% 1.47/1.03  
% 1.47/1.03  fof(f61,plain,(
% 1.47/1.03    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/1.03    inference(definition_unfolding,[],[f48,f57,f51,f59])).
% 1.47/1.03  
% 1.47/1.03  fof(f3,axiom,(
% 1.47/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f33,plain,(
% 1.47/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.47/1.03    inference(cnf_transformation,[],[f3])).
% 1.47/1.03  
% 1.47/1.03  fof(f4,axiom,(
% 1.47/1.03    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f34,plain,(
% 1.47/1.03    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.47/1.03    inference(cnf_transformation,[],[f4])).
% 1.47/1.03  
% 1.47/1.03  fof(f7,axiom,(
% 1.47/1.03    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f25,plain,(
% 1.47/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.47/1.03    inference(nnf_transformation,[],[f7])).
% 1.47/1.03  
% 1.47/1.03  fof(f26,plain,(
% 1.47/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.47/1.03    inference(rectify,[],[f25])).
% 1.47/1.03  
% 1.47/1.03  fof(f27,plain,(
% 1.47/1.03    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 1.47/1.03    introduced(choice_axiom,[])).
% 1.47/1.03  
% 1.47/1.03  fof(f28,plain,(
% 1.47/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.47/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 1.47/1.03  
% 1.47/1.03  fof(f44,plain,(
% 1.47/1.03    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.47/1.03    inference(cnf_transformation,[],[f28])).
% 1.47/1.03  
% 1.47/1.03  fof(f73,plain,(
% 1.47/1.03    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.47/1.03    inference(definition_unfolding,[],[f44,f59])).
% 1.47/1.03  
% 1.47/1.03  fof(f85,plain,(
% 1.47/1.03    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 1.47/1.03    inference(equality_resolution,[],[f73])).
% 1.47/1.03  
% 1.47/1.03  fof(f6,axiom,(
% 1.47/1.03    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.47/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.47/1.03  
% 1.47/1.03  fof(f18,plain,(
% 1.47/1.03    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.47/1.03    inference(ennf_transformation,[],[f6])).
% 1.47/1.03  
% 1.47/1.03  fof(f20,plain,(
% 1.47/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.47/1.03    inference(nnf_transformation,[],[f18])).
% 1.47/1.03  
% 1.47/1.03  fof(f21,plain,(
% 1.47/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.47/1.03    inference(flattening,[],[f20])).
% 1.47/1.03  
% 1.47/1.03  fof(f22,plain,(
% 1.47/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.47/1.03    inference(rectify,[],[f21])).
% 1.47/1.03  
% 1.47/1.03  fof(f23,plain,(
% 1.47/1.03    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 1.47/1.03    introduced(choice_axiom,[])).
% 1.47/1.03  
% 1.47/1.03  fof(f24,plain,(
% 1.47/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.47/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 1.47/1.03  
% 1.47/1.03  fof(f39,plain,(
% 1.47/1.03    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.47/1.03    inference(cnf_transformation,[],[f24])).
% 1.47/1.03  
% 1.47/1.03  fof(f66,plain,(
% 1.47/1.03    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.47/1.03    inference(definition_unfolding,[],[f39,f51])).
% 1.47/1.03  
% 1.47/1.03  fof(f76,plain,(
% 1.47/1.03    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.47/1.03    inference(equality_resolution,[],[f66])).
% 1.47/1.03  
% 1.47/1.03  fof(f77,plain,(
% 1.47/1.03    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.47/1.03    inference(equality_resolution,[],[f76])).
% 1.47/1.03  
% 1.47/1.03  fof(f45,plain,(
% 1.47/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.47/1.03    inference(cnf_transformation,[],[f28])).
% 1.47/1.03  
% 1.47/1.03  fof(f72,plain,(
% 1.47/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.47/1.03    inference(definition_unfolding,[],[f45,f59])).
% 1.47/1.03  
% 1.47/1.03  fof(f83,plain,(
% 1.47/1.03    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.47/1.03    inference(equality_resolution,[],[f72])).
% 1.47/1.03  
% 1.47/1.03  fof(f84,plain,(
% 1.47/1.03    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.47/1.03    inference(equality_resolution,[],[f83])).
% 1.47/1.03  
% 1.47/1.03  fof(f56,plain,(
% 1.47/1.03    sK2 != sK3),
% 1.47/1.03    inference(cnf_transformation,[],[f30])).
% 1.47/1.03  
% 1.47/1.03  cnf(c_1,plain,
% 1.47/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 1.47/1.03      inference(cnf_transformation,[],[f32]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_18,negated_conjecture,
% 1.47/1.03      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 1.47/1.03      inference(cnf_transformation,[],[f75]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_159,plain,
% 1.47/1.03      ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
% 1.47/1.03      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 1.47/1.03      | k3_xboole_0(X1,X0) = X1 ),
% 1.47/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_160,plain,
% 1.47/1.03      ( k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 1.47/1.03      inference(unflattening,[status(thm)],[c_159]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_0,plain,
% 1.47/1.03      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k5_xboole_0(k2_enumset1(X3,X3,X3,X3),k3_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2)))) = k2_enumset1(X0,X1,X2,X3) ),
% 1.47/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_1881,plain,
% 1.47/1.03      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) = k2_enumset1(sK3,sK3,sK3,sK2) ),
% 1.47/1.03      inference(superposition,[status(thm)],[c_160,c_0]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2,plain,
% 1.47/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.47/1.03      inference(cnf_transformation,[],[f33]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_3,plain,
% 1.47/1.03      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.47/1.03      inference(cnf_transformation,[],[f34]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_1882,plain,
% 1.47/1.03      ( k2_enumset1(sK3,sK3,sK3,sK2) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 1.47/1.03      inference(demodulation,[status(thm)],[c_1881,c_2,c_3]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2045,plain,
% 1.47/1.03      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK2),k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK3,sK3,sK3,sK2)))) = k2_enumset1(sK3,sK3,sK3,X0) ),
% 1.47/1.03      inference(superposition,[status(thm)],[c_1882,c_0]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2061,plain,
% 1.47/1.03      ( k2_enumset1(sK3,sK3,sK2,X0) = k2_enumset1(sK3,sK3,sK3,X0) ),
% 1.47/1.03      inference(demodulation,[status(thm)],[c_2045,c_0]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2079,plain,
% 1.47/1.03      ( k5_xboole_0(k2_enumset1(sK3,sK3,sK2,X0),k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(sK3,sK3,sK2,X0)))) = k2_enumset1(sK3,sK3,X0,X1) ),
% 1.47/1.03      inference(superposition,[status(thm)],[c_2061,c_0]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2096,plain,
% 1.47/1.03      ( k2_enumset1(sK3,sK2,X0,X1) = k2_enumset1(sK3,sK3,X0,X1) ),
% 1.47/1.03      inference(demodulation,[status(thm)],[c_2079,c_0]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2097,plain,
% 1.47/1.03      ( k2_enumset1(sK3,sK2,sK3,X0) = k2_enumset1(sK3,sK3,sK2,X0) ),
% 1.47/1.03      inference(demodulation,[status(thm)],[c_2096,c_2061]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2109,plain,
% 1.47/1.03      ( k2_enumset1(sK3,sK2,sK2,X0) = k2_enumset1(sK3,sK2,sK3,X0) ),
% 1.47/1.03      inference(demodulation,[status(thm)],[c_2097,c_2096]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_15,plain,
% 1.47/1.03      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 1.47/1.03      inference(cnf_transformation,[],[f85]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_1387,plain,
% 1.47/1.03      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 1.47/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2052,plain,
% 1.47/1.03      ( sK3 = X0
% 1.47/1.03      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK2)) != iProver_top ),
% 1.47/1.03      inference(superposition,[status(thm)],[c_1882,c_1387]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2361,plain,
% 1.47/1.03      ( sK3 = X0
% 1.47/1.03      | r2_hidden(X0,k2_enumset1(sK3,sK2,sK3,sK2)) != iProver_top ),
% 1.47/1.03      inference(demodulation,[status(thm)],[c_2052,c_2096]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_3022,plain,
% 1.47/1.03      ( sK3 = X0
% 1.47/1.03      | r2_hidden(X0,k2_enumset1(sK3,sK2,sK2,sK2)) != iProver_top ),
% 1.47/1.03      inference(demodulation,[status(thm)],[c_2109,c_2361]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_3037,plain,
% 1.47/1.03      ( sK3 = sK2
% 1.47/1.03      | r2_hidden(sK2,k2_enumset1(sK3,sK2,sK2,sK2)) != iProver_top ),
% 1.47/1.03      inference(instantiation,[status(thm)],[c_3022]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_8,plain,
% 1.47/1.03      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 1.47/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_1394,plain,
% 1.47/1.03      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 1.47/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2332,plain,
% 1.47/1.03      ( r2_hidden(X0,k2_enumset1(sK3,sK2,X1,X0)) = iProver_top ),
% 1.47/1.03      inference(superposition,[status(thm)],[c_2096,c_1394]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_2379,plain,
% 1.47/1.03      ( r2_hidden(sK2,k2_enumset1(sK3,sK2,sK2,sK2)) = iProver_top ),
% 1.47/1.03      inference(instantiation,[status(thm)],[c_2332]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_1193,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_1495,plain,
% 1.47/1.03      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 1.47/1.03      inference(instantiation,[status(thm)],[c_1193]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_1496,plain,
% 1.47/1.03      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 1.47/1.03      inference(instantiation,[status(thm)],[c_1495]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_14,plain,
% 1.47/1.03      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 1.47/1.03      inference(cnf_transformation,[],[f84]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_25,plain,
% 1.47/1.03      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 1.47/1.03      inference(instantiation,[status(thm)],[c_14]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_22,plain,
% 1.47/1.03      ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 1.47/1.03      inference(instantiation,[status(thm)],[c_15]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(c_17,negated_conjecture,
% 1.47/1.03      ( sK2 != sK3 ),
% 1.47/1.03      inference(cnf_transformation,[],[f56]) ).
% 1.47/1.03  
% 1.47/1.03  cnf(contradiction,plain,
% 1.47/1.03      ( $false ),
% 1.47/1.03      inference(minisat,
% 1.47/1.03                [status(thm)],
% 1.47/1.03                [c_3037,c_2379,c_1496,c_25,c_22,c_17]) ).
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.47/1.03  
% 1.47/1.03  ------                               Statistics
% 1.47/1.03  
% 1.47/1.03  ------ General
% 1.47/1.03  
% 1.47/1.03  abstr_ref_over_cycles:                  0
% 1.47/1.03  abstr_ref_under_cycles:                 0
% 1.47/1.03  gc_basic_clause_elim:                   0
% 1.47/1.03  forced_gc_time:                         0
% 1.47/1.03  parsing_time:                           0.018
% 1.47/1.03  unif_index_cands_time:                  0.
% 1.47/1.03  unif_index_add_time:                    0.
% 1.47/1.03  orderings_time:                         0.
% 1.47/1.03  out_proof_time:                         0.008
% 1.47/1.03  total_time:                             0.132
% 1.47/1.03  num_of_symbols:                         42
% 1.47/1.03  num_of_terms:                           3464
% 1.47/1.03  
% 1.47/1.03  ------ Preprocessing
% 1.47/1.03  
% 1.47/1.03  num_of_splits:                          0
% 1.47/1.03  num_of_split_atoms:                     0
% 1.47/1.03  num_of_reused_defs:                     0
% 1.47/1.03  num_eq_ax_congr_red:                    39
% 1.47/1.03  num_of_sem_filtered_clauses:            1
% 1.47/1.03  num_of_subtypes:                        0
% 1.47/1.03  monotx_restored_types:                  0
% 1.47/1.03  sat_num_of_epr_types:                   0
% 1.47/1.03  sat_num_of_non_cyclic_types:            0
% 1.47/1.03  sat_guarded_non_collapsed_types:        0
% 1.47/1.03  num_pure_diseq_elim:                    0
% 1.47/1.03  simp_replaced_by:                       0
% 1.47/1.03  res_preprocessed:                       86
% 1.47/1.03  prep_upred:                             0
% 1.47/1.03  prep_unflattend:                        74
% 1.47/1.03  smt_new_axioms:                         0
% 1.47/1.03  pred_elim_cands:                        1
% 1.47/1.03  pred_elim:                              1
% 1.47/1.03  pred_elim_cl:                           1
% 1.47/1.03  pred_elim_cycles:                       3
% 1.47/1.03  merged_defs:                            0
% 1.47/1.03  merged_defs_ncl:                        0
% 1.47/1.03  bin_hyper_res:                          0
% 1.47/1.03  prep_cycles:                            4
% 1.47/1.03  pred_elim_time:                         0.019
% 1.47/1.03  splitting_time:                         0.
% 1.47/1.03  sem_filter_time:                        0.
% 1.47/1.03  monotx_time:                            0.
% 1.47/1.03  subtype_inf_time:                       0.
% 1.47/1.03  
% 1.47/1.03  ------ Problem properties
% 1.47/1.03  
% 1.47/1.03  clauses:                                18
% 1.47/1.03  conjectures:                            1
% 1.47/1.03  epr:                                    1
% 1.47/1.03  horn:                                   15
% 1.47/1.03  ground:                                 2
% 1.47/1.03  unary:                                  10
% 1.47/1.03  binary:                                 1
% 1.47/1.03  lits:                                   36
% 1.47/1.03  lits_eq:                                24
% 1.47/1.03  fd_pure:                                0
% 1.47/1.03  fd_pseudo:                              0
% 1.47/1.03  fd_cond:                                0
% 1.47/1.03  fd_pseudo_cond:                         6
% 1.47/1.03  ac_symbols:                             0
% 1.47/1.03  
% 1.47/1.03  ------ Propositional Solver
% 1.47/1.03  
% 1.47/1.03  prop_solver_calls:                      26
% 1.47/1.03  prop_fast_solver_calls:                 622
% 1.47/1.03  smt_solver_calls:                       0
% 1.47/1.03  smt_fast_solver_calls:                  0
% 1.47/1.03  prop_num_of_clauses:                    792
% 1.47/1.03  prop_preprocess_simplified:             4012
% 1.47/1.03  prop_fo_subsumed:                       0
% 1.47/1.03  prop_solver_time:                       0.
% 1.47/1.03  smt_solver_time:                        0.
% 1.47/1.03  smt_fast_solver_time:                   0.
% 1.47/1.03  prop_fast_solver_time:                  0.
% 1.47/1.03  prop_unsat_core_time:                   0.
% 1.47/1.03  
% 1.47/1.03  ------ QBF
% 1.47/1.03  
% 1.47/1.03  qbf_q_res:                              0
% 1.47/1.03  qbf_num_tautologies:                    0
% 1.47/1.03  qbf_prep_cycles:                        0
% 1.47/1.03  
% 1.47/1.03  ------ BMC1
% 1.47/1.03  
% 1.47/1.03  bmc1_current_bound:                     -1
% 1.47/1.03  bmc1_last_solved_bound:                 -1
% 1.47/1.03  bmc1_unsat_core_size:                   -1
% 1.47/1.03  bmc1_unsat_core_parents_size:           -1
% 1.47/1.03  bmc1_merge_next_fun:                    0
% 1.47/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.47/1.03  
% 1.47/1.03  ------ Instantiation
% 1.47/1.03  
% 1.47/1.03  inst_num_of_clauses:                    274
% 1.47/1.03  inst_num_in_passive:                    118
% 1.47/1.03  inst_num_in_active:                     93
% 1.47/1.03  inst_num_in_unprocessed:                63
% 1.47/1.03  inst_num_of_loops:                      100
% 1.47/1.03  inst_num_of_learning_restarts:          0
% 1.47/1.03  inst_num_moves_active_passive:          6
% 1.47/1.03  inst_lit_activity:                      0
% 1.47/1.03  inst_lit_activity_moves:                0
% 1.47/1.03  inst_num_tautologies:                   0
% 1.47/1.03  inst_num_prop_implied:                  0
% 1.47/1.03  inst_num_existing_simplified:           0
% 1.47/1.03  inst_num_eq_res_simplified:             0
% 1.47/1.03  inst_num_child_elim:                    0
% 1.47/1.03  inst_num_of_dismatching_blockings:      72
% 1.47/1.03  inst_num_of_non_proper_insts:           243
% 1.47/1.03  inst_num_of_duplicates:                 0
% 1.47/1.03  inst_inst_num_from_inst_to_res:         0
% 1.47/1.03  inst_dismatching_checking_time:         0.
% 1.47/1.03  
% 1.47/1.03  ------ Resolution
% 1.47/1.03  
% 1.47/1.03  res_num_of_clauses:                     0
% 1.47/1.03  res_num_in_passive:                     0
% 1.47/1.03  res_num_in_active:                      0
% 1.47/1.03  res_num_of_loops:                       90
% 1.47/1.03  res_forward_subset_subsumed:            38
% 1.47/1.03  res_backward_subset_subsumed:           0
% 1.47/1.03  res_forward_subsumed:                   10
% 1.47/1.03  res_backward_subsumed:                  0
% 1.47/1.03  res_forward_subsumption_resolution:     0
% 1.47/1.03  res_backward_subsumption_resolution:    0
% 1.47/1.03  res_clause_to_clause_subsumption:       383
% 1.47/1.03  res_orphan_elimination:                 0
% 1.47/1.03  res_tautology_del:                      12
% 1.47/1.03  res_num_eq_res_simplified:              0
% 1.47/1.03  res_num_sel_changes:                    0
% 1.47/1.03  res_moves_from_active_to_pass:          0
% 1.47/1.03  
% 1.47/1.03  ------ Superposition
% 1.47/1.03  
% 1.47/1.03  sup_time_total:                         0.
% 1.47/1.03  sup_time_generating:                    0.
% 1.47/1.03  sup_time_sim_full:                      0.
% 1.47/1.03  sup_time_sim_immed:                     0.
% 1.47/1.03  
% 1.47/1.03  sup_num_of_clauses:                     32
% 1.47/1.03  sup_num_in_active:                      11
% 1.47/1.03  sup_num_in_passive:                     21
% 1.47/1.03  sup_num_of_loops:                       18
% 1.47/1.03  sup_fw_superposition:                   8
% 1.47/1.03  sup_bw_superposition:                   24
% 1.47/1.03  sup_immediate_simplified:               13
% 1.47/1.03  sup_given_eliminated:                   2
% 1.47/1.03  comparisons_done:                       0
% 1.47/1.03  comparisons_avoided:                    0
% 1.47/1.03  
% 1.47/1.03  ------ Simplifications
% 1.47/1.03  
% 1.47/1.03  
% 1.47/1.03  sim_fw_subset_subsumed:                 0
% 1.47/1.03  sim_bw_subset_subsumed:                 0
% 1.47/1.03  sim_fw_subsumed:                        6
% 1.47/1.03  sim_bw_subsumed:                        1
% 1.47/1.03  sim_fw_subsumption_res:                 0
% 1.47/1.03  sim_bw_subsumption_res:                 0
% 1.47/1.03  sim_tautology_del:                      0
% 1.47/1.03  sim_eq_tautology_del:                   1
% 1.47/1.03  sim_eq_res_simp:                        0
% 1.47/1.03  sim_fw_demodulated:                     18
% 1.47/1.03  sim_bw_demodulated:                     11
% 1.47/1.03  sim_light_normalised:                   1
% 1.47/1.03  sim_joinable_taut:                      0
% 1.47/1.03  sim_joinable_simp:                      0
% 1.47/1.03  sim_ac_normalised:                      0
% 1.47/1.03  sim_smt_subsumption:                    0
% 1.47/1.03  
%------------------------------------------------------------------------------
