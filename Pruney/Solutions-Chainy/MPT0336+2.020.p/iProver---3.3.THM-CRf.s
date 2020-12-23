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
% DateTime   : Thu Dec  3 11:38:37 EST 2020

% Result     : Theorem 27.84s
% Output     : CNFRefutation 27.84s
% Verified   : 
% Statistics : Number of formulae       :  395 (20793623 expanded)
%              Number of clauses        :  339 (7751839 expanded)
%              Number of leaves         :   18 (4930659 expanded)
%              Depth                    :   56
%              Number of atoms          :  483 (37685064 expanded)
%              Number of equality atoms :  372 (17289386 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f28])).

fof(f51,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f40,f40])).

fof(f49,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f60,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f49,f40,f55])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f24])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_203,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k2_xboole_0(X3,X1) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_204,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_1003,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_204])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_629,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_633,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1527,plain,
    ( k4_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_629,c_633])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1531,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1527,c_9])).

cnf(c_1537,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = sK3 ),
    inference(demodulation,[status(thm)],[c_1531,c_1527])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1632,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK3),X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1537,c_8])).

cnf(c_1911,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_1003,c_1632])).

cnf(c_1928,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_1911,c_1537])).

cnf(c_1929,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK3,X0))) = sK3 ),
    inference(demodulation,[status(thm)],[c_1928,c_8])).

cnf(c_2168,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(X0,sK3))) = sK3 ),
    inference(superposition,[status(thm)],[c_0,c_1929])).

cnf(c_2996,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_2168,c_9])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1082,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1003])).

cnf(c_3017,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))) = k2_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_2996,c_1082])).

cnf(c_3018,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK3),sK3) = k2_xboole_0(X0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_3017,c_1537])).

cnf(c_1208,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_1436,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1208,c_8])).

cnf(c_1448,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1436,c_8])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_209,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
    | k2_xboole_0(X1,X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_210,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_1197,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_12676,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_210,c_1197])).

cnf(c_13988,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_12676,c_1208])).

cnf(c_14041,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))) = k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(demodulation,[status(thm)],[c_13988,c_8,c_210])).

cnf(c_41392,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))) = k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_1448,c_14041])).

cnf(c_41144,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_210,c_1448])).

cnf(c_1083,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_204])).

cnf(c_43363,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_41144,c_1083])).

cnf(c_1189,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_7523,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1189,c_204])).

cnf(c_7605,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_7523,c_8])).

cnf(c_45016,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_43363,c_7605])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_634,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_43360,plain,
    ( k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK2
    | r1_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_41144,c_634])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_670,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X0,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_672,plain,
    ( ~ r2_hidden(sK4,sK2)
    | ~ r2_hidden(sK4,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5012,plain,
    ( r2_hidden(X0,sK2)
    | k4_xboole_0(sK2,k3_enumset1(X0,X0,X0,X0,X0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5014,plain,
    ( r2_hidden(sK4,sK2)
    | k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK2 ),
    inference(instantiation,[status(thm)],[c_5012])).

cnf(c_44681,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43360,c_16,c_15,c_672,c_5014])).

cnf(c_44686,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = sK2 ),
    inference(superposition,[status(thm)],[c_44681,c_633])).

cnf(c_45027,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_45016,c_44686])).

cnf(c_45028,plain,
    ( k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_45027,c_1003])).

cnf(c_48435,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_41392,c_41392,c_45028])).

cnf(c_7522,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
    inference(superposition,[status(thm)],[c_1189,c_1003])).

cnf(c_7606,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
    inference(demodulation,[status(thm)],[c_7522,c_8])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_638,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6276,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_629,c_638])).

cnf(c_6867,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_6276,c_633])).

cnf(c_6994,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_6867,c_8])).

cnf(c_10389,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK3),X1))) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_7606,c_6994])).

cnf(c_10412,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK3),X1))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_10389,c_6867])).

cnf(c_10792,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,sK3)))) = sK2 ),
    inference(superposition,[status(thm)],[c_0,c_10412])).

cnf(c_16582,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_10792,c_9])).

cnf(c_1532,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1527,c_8])).

cnf(c_1756,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1003,c_1532])).

cnf(c_1773,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK2,X0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_1756,c_1527])).

cnf(c_2197,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK2,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1773,c_1083])).

cnf(c_2838,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3))) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_2197,c_1082])).

cnf(c_1535,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1527,c_1208])).

cnf(c_2839,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_2838,c_1535])).

cnf(c_3597,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK3,sK3),X0) ),
    inference(superposition,[status(thm)],[c_2839,c_8])).

cnf(c_2184,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,X0)),k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1929,c_1082])).

cnf(c_1195,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_204])).

cnf(c_2186,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_2184,c_1195])).

cnf(c_3616,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK3),X0)) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_3597,c_8,c_2186])).

cnf(c_5063,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_204,c_3616])).

cnf(c_14408,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_1003,c_14041])).

cnf(c_9982,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_210,c_7605])).

cnf(c_10482,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_9982,c_7606])).

cnf(c_7515,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK2),X0)) = k4_xboole_0(k4_xboole_0(sK2,sK2),X0) ),
    inference(superposition,[status(thm)],[c_6867,c_1189])).

cnf(c_7612,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK3),X0) = k4_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_7515,c_1527,c_2186,c_5063])).

cnf(c_12821,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK3,sK3)))) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1197,c_7612])).

cnf(c_1429,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_1208])).

cnf(c_1452,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_1429,c_1208])).

cnf(c_1453,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_1452,c_8])).

cnf(c_8616,plain,
    ( k2_xboole_0(X0,k4_xboole_0(sK3,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_7612,c_1082])).

cnf(c_12836,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_12821,c_8,c_1453,c_8616])).

cnf(c_13205,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_10482,c_12836])).

cnf(c_14474,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_14408,c_13205])).

cnf(c_1432,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_9,c_1208])).

cnf(c_1450,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1432,c_8,c_204])).

cnf(c_7507,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_1189])).

cnf(c_14475,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_14474,c_1003,c_1450,c_7507])).

cnf(c_16605,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_16582,c_5063,c_6867,c_14475])).

cnf(c_1336,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1082])).

cnf(c_1338,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = X0 ),
    inference(demodulation,[status(thm)],[c_1336,c_8])).

cnf(c_18619,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_10482,c_1338])).

cnf(c_14008,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))) = k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_12676,c_1208])).

cnf(c_1194,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_1003])).

cnf(c_9580,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_210,c_1194])).

cnf(c_13239,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_9580,c_12836])).

cnf(c_14019,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))) = k4_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_14008,c_13239])).

cnf(c_14020,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))))) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_14019,c_8])).

cnf(c_1444,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1208,c_8])).

cnf(c_1445,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1444,c_8])).

cnf(c_14021,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_14020,c_1445])).

cnf(c_14022,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_14021,c_210])).

cnf(c_13264,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_12836,c_1197])).

cnf(c_13290,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK3,sK3)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_13264,c_9])).

cnf(c_16968,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK1,sK1)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_13290,c_13290,c_14475])).

cnf(c_17026,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_14022,c_16968])).

cnf(c_17103,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_17026,c_16968])).

cnf(c_17104,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_17103,c_14022,c_14475])).

cnf(c_18771,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_18619,c_17104])).

cnf(c_48436,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_48435,c_1208,c_1448,c_16605,c_18771])).

cnf(c_48465,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_48436,c_8])).

cnf(c_49880,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(k4_xboole_0(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_48465,c_8])).

cnf(c_1191,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_8,c_8])).

cnf(c_1200,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_1191,c_8])).

cnf(c_49976,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_49880,c_8,c_1200])).

cnf(c_7377,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k4_xboole_0(k4_xboole_0(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_6994,c_8])).

cnf(c_7393,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k4_xboole_0(sK2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_7377,c_8,c_1200])).

cnf(c_38514,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK3,X1))) = k4_xboole_0(sK2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_7393])).

cnf(c_10325,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_7606])).

cnf(c_18000,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X2)) ),
    inference(superposition,[status(thm)],[c_9580,c_1200])).

cnf(c_32324,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
    inference(superposition,[status(thm)],[c_10325,c_18000])).

cnf(c_32435,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_32324,c_9580])).

cnf(c_11129,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_0,c_1195])).

cnf(c_64194,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))),k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) ),
    inference(superposition,[status(thm)],[c_32435,c_11129])).

cnf(c_36285,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_32435,c_8])).

cnf(c_36333,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(demodulation,[status(thm)],[c_36285,c_8])).

cnf(c_41246,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))),X1)) = k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1)) ),
    inference(superposition,[status(thm)],[c_12676,c_1448])).

cnf(c_15023,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_13239,c_13239,c_14475])).

cnf(c_15046,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),X1) ),
    inference(superposition,[status(thm)],[c_15023,c_8])).

cnf(c_13201,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_0,c_12836])).

cnf(c_15077,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1)) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_15046,c_8,c_13201])).

cnf(c_15078,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_15077,c_14475])).

cnf(c_41515,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))),X1)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_41246,c_15078])).

cnf(c_1198,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_1199,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_1198,c_8])).

cnf(c_1210,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_1223,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1210,c_8])).

cnf(c_26698,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1199,c_1223])).

cnf(c_41516,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),X1))) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_41515,c_8,c_26698])).

cnf(c_41517,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X1))) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_41516,c_210])).

cnf(c_41177,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1208,c_1448])).

cnf(c_41181,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_1448])).

cnf(c_41584,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_41181,c_1208])).

cnf(c_41585,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_41584,c_8])).

cnf(c_41593,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_41177,c_41585])).

cnf(c_1217,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_1218,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1217,c_8])).

cnf(c_1219,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1218,c_8])).

cnf(c_20952,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1003,c_1219])).

cnf(c_41594,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_41593,c_8,c_20952])).

cnf(c_41896,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_41594,c_8])).

cnf(c_41774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_41594])).

cnf(c_17964,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X1))) = k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X1)) ),
    inference(superposition,[status(thm)],[c_210,c_1200])).

cnf(c_19362,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)) ),
    inference(superposition,[status(thm)],[c_17964,c_1189])).

cnf(c_42401,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X1)),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)) ),
    inference(superposition,[status(thm)],[c_41774,c_19362])).

cnf(c_42406,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X1)),X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)),X2) ),
    inference(superposition,[status(thm)],[c_41774,c_1189])).

cnf(c_9981,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(superposition,[status(thm)],[c_204,c_7605])).

cnf(c_42519,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X1)),X2)) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_42406,c_8,c_9981])).

cnf(c_42520,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X1)),X2)) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_42519,c_20952])).

cnf(c_42526,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X1)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_42401,c_42520])).

cnf(c_41865,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_41594,c_1197])).

cnf(c_41875,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X0),X2) ),
    inference(superposition,[status(thm)],[c_41594,c_8])).

cnf(c_41174,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_1199,c_1448])).

cnf(c_1214,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_1220,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1214,c_8])).

cnf(c_23835,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_8,c_1220])).

cnf(c_15760,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_1199,c_1197])).

cnf(c_24113,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_23835,c_15760])).

cnf(c_24114,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_24113,c_8])).

cnf(c_41596,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_41174,c_24114])).

cnf(c_42023,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_41875,c_8,c_20952,c_41596])).

cnf(c_42034,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_41865,c_41594,c_42023])).

cnf(c_15732,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1199,c_13201])).

cnf(c_13396,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_13201,c_1197])).

cnf(c_13416,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_13396,c_13290])).

cnf(c_15785,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_15732,c_13416,c_14475])).

cnf(c_42035,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_42034,c_15785])).

cnf(c_42527,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_42526,c_42035])).

cnf(c_42528,plain,
    ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_42527])).

cnf(c_42546,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_41896,c_41896,c_42528])).

cnf(c_14107,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k2_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_8,c_14022])).

cnf(c_15117,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k2_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_14107,c_14107,c_14475])).

cnf(c_15198,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_210,c_15117])).

cnf(c_17200,plain,
    ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1003,c_15198])).

cnf(c_36854,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK1)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
    inference(superposition,[status(thm)],[c_17200,c_19362])).

cnf(c_17228,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_15198,c_8])).

cnf(c_11132,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_210,c_1195])).

cnf(c_11627,plain,
    ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_11132,c_1189])).

cnf(c_20686,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_17228,c_11627])).

cnf(c_17329,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1003,c_17104])).

cnf(c_20689,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(light_normalisation,[status(thm)],[c_20686,c_17329])).

cnf(c_13243,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_11132,c_12836])).

cnf(c_14669,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_13243,c_13243,c_14475])).

cnf(c_14696,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_14669,c_204])).

cnf(c_17347,plain,
    ( k2_xboole_0(X0,k4_xboole_0(sK1,sK1)) = X0 ),
    inference(superposition,[status(thm)],[c_17104,c_1003])).

cnf(c_19343,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0))) ),
    inference(superposition,[status(thm)],[c_17964,c_1])).

cnf(c_19371,plain,
    ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_17964,c_11627])).

cnf(c_17021,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,sK1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_13201,c_16968])).

cnf(c_17109,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_17021,c_16968])).

cnf(c_17110,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_17109,c_13201,c_14475])).

cnf(c_19376,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(demodulation,[status(thm)],[c_19371,c_8,c_7507,c_17110])).

cnf(c_19377,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_19376,c_14696])).

cnf(c_19384,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0))) ),
    inference(demodulation,[status(thm)],[c_19343,c_19377])).

cnf(c_19373,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_17964,c_13201])).

cnf(c_19374,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_19373,c_14475])).

cnf(c_19385,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK1)) ),
    inference(demodulation,[status(thm)],[c_19384,c_19374])).

cnf(c_13240,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_9982,c_12836])).

cnf(c_14500,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_13240,c_13240,c_14475])).

cnf(c_14513,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_14500,c_1003])).

cnf(c_19386,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_19385,c_7507,c_14513])).

cnf(c_20690,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_20689,c_8,c_210,c_14696,c_17347,c_19386])).

cnf(c_37261,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK1)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
    inference(light_normalisation,[status(thm)],[c_36854,c_20690])).

cnf(c_17348,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_17104,c_204])).

cnf(c_17630,plain,
    ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(k4_xboole_0(sK1,sK1),X0) ),
    inference(superposition,[status(thm)],[c_17200,c_8])).

cnf(c_16991,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,sK1)) = k4_xboole_0(k4_xboole_0(sK3,sK3),X0) ),
    inference(superposition,[status(thm)],[c_7612,c_16968])).

cnf(c_17151,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK3),X0) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_16991,c_16968])).

cnf(c_17152,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_17151,c_7612,c_14475])).

cnf(c_17681,plain,
    ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_17630,c_17152])).

cnf(c_19349,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)) ),
    inference(superposition,[status(thm)],[c_17964,c_8])).

cnf(c_19383,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2))) ),
    inference(demodulation,[status(thm)],[c_19349,c_8])).

cnf(c_37262,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_37261,c_8,c_17348,c_17681,c_17964,c_19383])).

cnf(c_42723,plain,
    ( k4_xboole_0(sK1,sK1) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_42546,c_37262])).

cnf(c_43611,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X1))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_41517,c_41517,c_42723])).

cnf(c_43637,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK2))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_9982,c_43611])).

cnf(c_43836,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sP0_iProver_split)) ),
    inference(superposition,[status(thm)],[c_43637,c_9])).

cnf(c_43891,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sP0_iProver_split)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_43836,c_43637])).

cnf(c_48475,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_48436,c_1208])).

cnf(c_1434,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1208,c_1083])).

cnf(c_28710,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1434,c_12836])).

cnf(c_28745,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_28710,c_1450,c_14475])).

cnf(c_45032,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_1450,c_28745,c_42528])).

cnf(c_45208,plain,
    ( k4_xboole_0(sK2,sK2) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_10412,c_45032])).

cnf(c_48488,plain,
    ( k4_xboole_0(sK1,sP0_iProver_split) = k4_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_48475,c_45208])).

cnf(c_64320,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X4,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),k4_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split))) ),
    inference(light_normalisation,[status(thm)],[c_64194,c_36333,c_43891,c_48488])).

cnf(c_8608,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK3),X0) = X0 ),
    inference(superposition,[status(thm)],[c_7612,c_1083])).

cnf(c_1431,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_1208])).

cnf(c_1451,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1431,c_8])).

cnf(c_48999,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_8608,c_1451])).

cnf(c_42721,plain,
    ( k4_xboole_0(sK3,sK3) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_42546,c_13201])).

cnf(c_49311,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(sP0_iProver_split,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_48999,c_42721])).

cnf(c_45192,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_9,c_45032])).

cnf(c_46589,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_45192,c_204])).

cnf(c_49312,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_49311,c_1208,c_46589])).

cnf(c_64321,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X4,k4_xboole_0(X1,sP0_iProver_split))),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_64320,c_43891,c_48488,c_49312])).

cnf(c_64323,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = sP2_iProver_split(X0,X1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_64321])).

cnf(c_32317,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
    inference(superposition,[status(thm)],[c_1338,c_18000])).

cnf(c_32439,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_32317,c_9580])).

cnf(c_64260,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_11129,c_32439])).

cnf(c_64266,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_64260,c_43891,c_48488,c_49312])).

cnf(c_64325,plain,
    ( sP2_iProver_split(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_64323,c_64266])).

cnf(c_83401,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK3,X1))) = sP2_iProver_split(sK2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_38514,c_64325])).

cnf(c_83538,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_83401,c_6994])).

cnf(c_1764,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,X0),X1)) = k4_xboole_0(k4_xboole_0(sK3,X0),X1) ),
    inference(superposition,[status(thm)],[c_1532,c_8])).

cnf(c_1769,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,X0),X1)) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1764,c_8,c_1200])).

cnf(c_21570,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k4_xboole_0(sK3,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1769])).

cnf(c_1754,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1532])).

cnf(c_1893,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,sK2),X1)) = k4_xboole_0(k4_xboole_0(sK3,X0),X1) ),
    inference(superposition,[status(thm)],[c_1754,c_8])).

cnf(c_1898,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,sK2),X1)) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1893,c_8,c_1200])).

cnf(c_21811,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1898,c_1200])).

cnf(c_75864,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = sP2_iProver_split(sK3,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_21570,c_21811,c_64325])).

cnf(c_42571,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X0))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_0,c_42546])).

cnf(c_76036,plain,
    ( sP2_iProver_split(sK3,k2_xboole_0(sK3,sK3)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_75864,c_42571])).

cnf(c_1533,plain,
    ( k2_xboole_0(sK3,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1527,c_1003])).

cnf(c_76041,plain,
    ( sP2_iProver_split(sK3,sK3) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_76036,c_1533])).

cnf(c_7369,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1003,c_6994])).

cnf(c_7398,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_7369,c_6867])).

cnf(c_8686,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK3,X0),X1)) = k4_xboole_0(sK2,X1) ),
    inference(superposition,[status(thm)],[c_7398,c_8])).

cnf(c_11330,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK3,X1))) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_8686])).

cnf(c_16660,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK3)))) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1,c_11330])).

cnf(c_71817,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(X0,sP2_iProver_split(X1,k4_xboole_0(X1,sK3)))) = sP2_iProver_split(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_16660,c_64325])).

cnf(c_71818,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(X0,sP2_iProver_split(X1,sP2_iProver_split(X1,sK3)))) = sP2_iProver_split(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_71817,c_64325])).

cnf(c_83052,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(X0,sP2_iProver_split(sK3,sP0_iProver_split))) = sP2_iProver_split(sK2,X0) ),
    inference(superposition,[status(thm)],[c_76041,c_71818])).

cnf(c_34356,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_20690,c_1445])).

cnf(c_34704,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_34356,c_210,c_17329])).

cnf(c_41266,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1)),X0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
    inference(superposition,[status(thm)],[c_34704,c_1448])).

cnf(c_78093,plain,
    ( k4_xboole_0(k2_xboole_0(sP0_iProver_split,k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split)),k2_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split),X0)) = k4_xboole_0(k2_xboole_0(sP0_iProver_split,k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
    inference(light_normalisation,[status(thm)],[c_41266,c_41266,c_42723,c_43891,c_48488])).

cnf(c_8615,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK3,sK3)),X1)) = k4_xboole_0(k4_xboole_0(sK3,sK3),X1) ),
    inference(superposition,[status(thm)],[c_7612,c_1189])).

cnf(c_8640,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK3,sK3)),X1)) = k4_xboole_0(sK3,sK3) ),
    inference(demodulation,[status(thm)],[c_8615,c_7612])).

cnf(c_10871,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(sK3,sK3)))) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_0,c_8640])).

cnf(c_57206,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,sP0_iProver_split))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_10871,c_10871,c_42721])).

cnf(c_57293,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split)),k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),X2)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split)),k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_57206,c_1448])).

cnf(c_78094,plain,
    ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(sP0_iProver_split,k2_xboole_0(sP2_iProver_split(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split),X0))) = sP2_iProver_split(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
    inference(demodulation,[status(thm)],[c_78093,c_41596,c_46589,c_57293,c_64325])).

cnf(c_17047,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_16968,c_7606])).

cnf(c_15221,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_15117,c_204])).

cnf(c_17076,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_17047,c_8,c_15221])).

cnf(c_71874,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sP2_iProver_split(X0,X1),X2))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_17076,c_17076,c_42723,c_64325])).

cnf(c_78095,plain,
    ( sP2_iProver_split(sP2_iProver_split(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_78094,c_64325,c_71874])).

cnf(c_2199,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK2,X0),X1)) = k4_xboole_0(sK3,X1) ),
    inference(superposition,[status(thm)],[c_1773,c_8])).

cnf(c_3246,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK2,X1))) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2199])).

cnf(c_10055,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,X1)),X2))) = k4_xboole_0(sK3,k4_xboole_0(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_7605,c_3246])).

cnf(c_10060,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,X1)),X2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_10055,c_1773])).

cnf(c_12486,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(sK2,X2))))) = sK3 ),
    inference(superposition,[status(thm)],[c_0,c_10060])).

cnf(c_64390,plain,
    ( sP2_iProver_split(sK3,sP2_iProver_split(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(sK2,X2))))) = sK3 ),
    inference(demodulation,[status(thm)],[c_12486,c_64325])).

cnf(c_64391,plain,
    ( sP2_iProver_split(sK3,sP2_iProver_split(X0,k2_xboole_0(X1,sP2_iProver_split(X0,k4_xboole_0(sK2,X2))))) = sK3 ),
    inference(demodulation,[status(thm)],[c_64390,c_64325])).

cnf(c_64392,plain,
    ( sP2_iProver_split(sK3,sP2_iProver_split(X0,k2_xboole_0(X1,sP2_iProver_split(X0,sP2_iProver_split(sK2,X2))))) = sK3 ),
    inference(demodulation,[status(thm)],[c_64391,c_64325])).

cnf(c_78115,plain,
    ( sP2_iProver_split(sK3,sP0_iProver_split) = sK3 ),
    inference(superposition,[status(thm)],[c_78095,c_64392])).

cnf(c_83067,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(X0,sK3)) = sP2_iProver_split(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_83052,c_78115])).

cnf(c_83640,plain,
    ( sP2_iProver_split(sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_83538,c_6994,c_83067])).

cnf(c_87875,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = sP2_iProver_split(sK2,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_49976,c_83640])).

cnf(c_87906,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(sK3,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_3018,c_87875])).

cnf(c_6996,plain,
    ( k2_xboole_0(sK2,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_6867,c_1003])).

cnf(c_21747,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK2))) = k4_xboole_0(sK3,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1898])).

cnf(c_75919,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK2))) = sP2_iProver_split(sK3,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_75864])).

cnf(c_76450,plain,
    ( sP2_iProver_split(sK3,k2_xboole_0(X0,X1)) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_21747,c_75919])).

cnf(c_76553,plain,
    ( sP2_iProver_split(sK3,k2_xboole_0(sK2,sK2)) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_6996,c_76450])).

cnf(c_77200,plain,
    ( sP2_iProver_split(sK3,sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_76553,c_1527,c_6996])).

cnf(c_1767,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
    inference(superposition,[status(thm)],[c_1532,c_1208])).

cnf(c_66950,plain,
    ( sP2_iProver_split(k2_xboole_0(sK2,X0),sP2_iProver_split(sK3,k4_xboole_0(sK3,X0))) = sP2_iProver_split(k2_xboole_0(sK2,X0),sK3) ),
    inference(demodulation,[status(thm)],[c_1767,c_64325])).

cnf(c_66951,plain,
    ( sP2_iProver_split(k2_xboole_0(sK2,X0),sP2_iProver_split(sK3,sP2_iProver_split(sK3,X0))) = sP2_iProver_split(k2_xboole_0(sK2,X0),sK3) ),
    inference(demodulation,[status(thm)],[c_66950,c_64325])).

cnf(c_77403,plain,
    ( sP2_iProver_split(k2_xboole_0(sK2,sK2),sP2_iProver_split(sK3,sK3)) = sP2_iProver_split(k2_xboole_0(sK2,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_77200,c_66951])).

cnf(c_77404,plain,
    ( sP2_iProver_split(sK2,sP0_iProver_split) = sP2_iProver_split(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_77403,c_6996,c_76041])).

cnf(c_88197,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = sP2_iProver_split(sK2,sP0_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_87906,c_1533,c_77404])).

cnf(c_3011,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)),k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_2996,c_1083])).

cnf(c_3023,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_3011,c_1537])).

cnf(c_83436,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(sK3,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK3)) ),
    inference(superposition,[status(thm)],[c_3023,c_83401])).

cnf(c_83459,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_1533,c_83401])).

cnf(c_3648,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_0,c_3023])).

cnf(c_7371,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_3648,c_6994])).

cnf(c_7396,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_7371,c_6994])).

cnf(c_83759,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_83459,c_7396])).

cnf(c_83760,plain,
    ( sP2_iProver_split(sK2,k2_xboole_0(sK3,X0)) = sP2_iProver_split(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_83759,c_64325])).

cnf(c_83794,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK3)) = sP2_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_83436,c_83640,c_83760])).

cnf(c_83795,plain,
    ( sP2_iProver_split(sK2,sP0_iProver_split) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_83794,c_1533,c_6867,c_77404])).

cnf(c_88198,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_88197,c_48465,c_83795])).

cnf(c_723,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
    | k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != sK2 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_662,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88198,c_723,c_662,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:10:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.84/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.84/4.00  
% 27.84/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.84/4.00  
% 27.84/4.00  ------  iProver source info
% 27.84/4.00  
% 27.84/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.84/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.84/4.00  git: non_committed_changes: false
% 27.84/4.00  git: last_make_outside_of_git: false
% 27.84/4.00  
% 27.84/4.00  ------ 
% 27.84/4.00  
% 27.84/4.00  ------ Input Options
% 27.84/4.00  
% 27.84/4.00  --out_options                           all
% 27.84/4.00  --tptp_safe_out                         true
% 27.84/4.00  --problem_path                          ""
% 27.84/4.00  --include_path                          ""
% 27.84/4.00  --clausifier                            res/vclausify_rel
% 27.84/4.00  --clausifier_options                    ""
% 27.84/4.00  --stdin                                 false
% 27.84/4.00  --stats_out                             all
% 27.84/4.00  
% 27.84/4.00  ------ General Options
% 27.84/4.00  
% 27.84/4.00  --fof                                   false
% 27.84/4.00  --time_out_real                         305.
% 27.84/4.00  --time_out_virtual                      -1.
% 27.84/4.00  --symbol_type_check                     false
% 27.84/4.00  --clausify_out                          false
% 27.84/4.00  --sig_cnt_out                           false
% 27.84/4.00  --trig_cnt_out                          false
% 27.84/4.00  --trig_cnt_out_tolerance                1.
% 27.84/4.00  --trig_cnt_out_sk_spl                   false
% 27.84/4.00  --abstr_cl_out                          false
% 27.84/4.00  
% 27.84/4.00  ------ Global Options
% 27.84/4.00  
% 27.84/4.00  --schedule                              default
% 27.84/4.00  --add_important_lit                     false
% 27.84/4.00  --prop_solver_per_cl                    1000
% 27.84/4.00  --min_unsat_core                        false
% 27.84/4.00  --soft_assumptions                      false
% 27.84/4.00  --soft_lemma_size                       3
% 27.84/4.00  --prop_impl_unit_size                   0
% 27.84/4.00  --prop_impl_unit                        []
% 27.84/4.00  --share_sel_clauses                     true
% 27.84/4.00  --reset_solvers                         false
% 27.84/4.00  --bc_imp_inh                            [conj_cone]
% 27.84/4.00  --conj_cone_tolerance                   3.
% 27.84/4.00  --extra_neg_conj                        none
% 27.84/4.00  --large_theory_mode                     true
% 27.84/4.00  --prolific_symb_bound                   200
% 27.84/4.00  --lt_threshold                          2000
% 27.84/4.00  --clause_weak_htbl                      true
% 27.84/4.00  --gc_record_bc_elim                     false
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing Options
% 27.84/4.00  
% 27.84/4.00  --preprocessing_flag                    true
% 27.84/4.00  --time_out_prep_mult                    0.1
% 27.84/4.00  --splitting_mode                        input
% 27.84/4.00  --splitting_grd                         true
% 27.84/4.00  --splitting_cvd                         false
% 27.84/4.00  --splitting_cvd_svl                     false
% 27.84/4.00  --splitting_nvd                         32
% 27.84/4.00  --sub_typing                            true
% 27.84/4.00  --prep_gs_sim                           true
% 27.84/4.00  --prep_unflatten                        true
% 27.84/4.00  --prep_res_sim                          true
% 27.84/4.00  --prep_upred                            true
% 27.84/4.00  --prep_sem_filter                       exhaustive
% 27.84/4.00  --prep_sem_filter_out                   false
% 27.84/4.00  --pred_elim                             true
% 27.84/4.00  --res_sim_input                         true
% 27.84/4.00  --eq_ax_congr_red                       true
% 27.84/4.00  --pure_diseq_elim                       true
% 27.84/4.00  --brand_transform                       false
% 27.84/4.00  --non_eq_to_eq                          false
% 27.84/4.00  --prep_def_merge                        true
% 27.84/4.00  --prep_def_merge_prop_impl              false
% 27.84/4.00  --prep_def_merge_mbd                    true
% 27.84/4.00  --prep_def_merge_tr_red                 false
% 27.84/4.00  --prep_def_merge_tr_cl                  false
% 27.84/4.00  --smt_preprocessing                     true
% 27.84/4.00  --smt_ac_axioms                         fast
% 27.84/4.00  --preprocessed_out                      false
% 27.84/4.00  --preprocessed_stats                    false
% 27.84/4.00  
% 27.84/4.00  ------ Abstraction refinement Options
% 27.84/4.00  
% 27.84/4.00  --abstr_ref                             []
% 27.84/4.00  --abstr_ref_prep                        false
% 27.84/4.00  --abstr_ref_until_sat                   false
% 27.84/4.00  --abstr_ref_sig_restrict                funpre
% 27.84/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.84/4.00  --abstr_ref_under                       []
% 27.84/4.00  
% 27.84/4.00  ------ SAT Options
% 27.84/4.00  
% 27.84/4.00  --sat_mode                              false
% 27.84/4.00  --sat_fm_restart_options                ""
% 27.84/4.00  --sat_gr_def                            false
% 27.84/4.00  --sat_epr_types                         true
% 27.84/4.00  --sat_non_cyclic_types                  false
% 27.84/4.00  --sat_finite_models                     false
% 27.84/4.00  --sat_fm_lemmas                         false
% 27.84/4.00  --sat_fm_prep                           false
% 27.84/4.00  --sat_fm_uc_incr                        true
% 27.84/4.00  --sat_out_model                         small
% 27.84/4.00  --sat_out_clauses                       false
% 27.84/4.00  
% 27.84/4.00  ------ QBF Options
% 27.84/4.00  
% 27.84/4.00  --qbf_mode                              false
% 27.84/4.00  --qbf_elim_univ                         false
% 27.84/4.00  --qbf_dom_inst                          none
% 27.84/4.00  --qbf_dom_pre_inst                      false
% 27.84/4.00  --qbf_sk_in                             false
% 27.84/4.00  --qbf_pred_elim                         true
% 27.84/4.00  --qbf_split                             512
% 27.84/4.00  
% 27.84/4.00  ------ BMC1 Options
% 27.84/4.00  
% 27.84/4.00  --bmc1_incremental                      false
% 27.84/4.00  --bmc1_axioms                           reachable_all
% 27.84/4.00  --bmc1_min_bound                        0
% 27.84/4.00  --bmc1_max_bound                        -1
% 27.84/4.00  --bmc1_max_bound_default                -1
% 27.84/4.00  --bmc1_symbol_reachability              true
% 27.84/4.00  --bmc1_property_lemmas                  false
% 27.84/4.00  --bmc1_k_induction                      false
% 27.84/4.00  --bmc1_non_equiv_states                 false
% 27.84/4.00  --bmc1_deadlock                         false
% 27.84/4.00  --bmc1_ucm                              false
% 27.84/4.00  --bmc1_add_unsat_core                   none
% 27.84/4.00  --bmc1_unsat_core_children              false
% 27.84/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.84/4.00  --bmc1_out_stat                         full
% 27.84/4.00  --bmc1_ground_init                      false
% 27.84/4.00  --bmc1_pre_inst_next_state              false
% 27.84/4.00  --bmc1_pre_inst_state                   false
% 27.84/4.00  --bmc1_pre_inst_reach_state             false
% 27.84/4.00  --bmc1_out_unsat_core                   false
% 27.84/4.00  --bmc1_aig_witness_out                  false
% 27.84/4.00  --bmc1_verbose                          false
% 27.84/4.00  --bmc1_dump_clauses_tptp                false
% 27.84/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.84/4.00  --bmc1_dump_file                        -
% 27.84/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.84/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.84/4.00  --bmc1_ucm_extend_mode                  1
% 27.84/4.00  --bmc1_ucm_init_mode                    2
% 27.84/4.00  --bmc1_ucm_cone_mode                    none
% 27.84/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.84/4.00  --bmc1_ucm_relax_model                  4
% 27.84/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.84/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.84/4.00  --bmc1_ucm_layered_model                none
% 27.84/4.00  --bmc1_ucm_max_lemma_size               10
% 27.84/4.00  
% 27.84/4.00  ------ AIG Options
% 27.84/4.00  
% 27.84/4.00  --aig_mode                              false
% 27.84/4.00  
% 27.84/4.00  ------ Instantiation Options
% 27.84/4.00  
% 27.84/4.00  --instantiation_flag                    true
% 27.84/4.00  --inst_sos_flag                         true
% 27.84/4.00  --inst_sos_phase                        true
% 27.84/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.84/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.84/4.00  --inst_lit_sel_side                     num_symb
% 27.84/4.00  --inst_solver_per_active                1400
% 27.84/4.00  --inst_solver_calls_frac                1.
% 27.84/4.00  --inst_passive_queue_type               priority_queues
% 27.84/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.84/4.00  --inst_passive_queues_freq              [25;2]
% 27.84/4.00  --inst_dismatching                      true
% 27.84/4.00  --inst_eager_unprocessed_to_passive     true
% 27.84/4.00  --inst_prop_sim_given                   true
% 27.84/4.00  --inst_prop_sim_new                     false
% 27.84/4.00  --inst_subs_new                         false
% 27.84/4.00  --inst_eq_res_simp                      false
% 27.84/4.00  --inst_subs_given                       false
% 27.84/4.00  --inst_orphan_elimination               true
% 27.84/4.00  --inst_learning_loop_flag               true
% 27.84/4.00  --inst_learning_start                   3000
% 27.84/4.00  --inst_learning_factor                  2
% 27.84/4.00  --inst_start_prop_sim_after_learn       3
% 27.84/4.00  --inst_sel_renew                        solver
% 27.84/4.00  --inst_lit_activity_flag                true
% 27.84/4.00  --inst_restr_to_given                   false
% 27.84/4.00  --inst_activity_threshold               500
% 27.84/4.00  --inst_out_proof                        true
% 27.84/4.00  
% 27.84/4.00  ------ Resolution Options
% 27.84/4.00  
% 27.84/4.00  --resolution_flag                       true
% 27.84/4.00  --res_lit_sel                           adaptive
% 27.84/4.00  --res_lit_sel_side                      none
% 27.84/4.00  --res_ordering                          kbo
% 27.84/4.00  --res_to_prop_solver                    active
% 27.84/4.00  --res_prop_simpl_new                    false
% 27.84/4.00  --res_prop_simpl_given                  true
% 27.84/4.00  --res_passive_queue_type                priority_queues
% 27.84/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.84/4.00  --res_passive_queues_freq               [15;5]
% 27.84/4.00  --res_forward_subs                      full
% 27.84/4.00  --res_backward_subs                     full
% 27.84/4.00  --res_forward_subs_resolution           true
% 27.84/4.00  --res_backward_subs_resolution          true
% 27.84/4.00  --res_orphan_elimination                true
% 27.84/4.00  --res_time_limit                        2.
% 27.84/4.00  --res_out_proof                         true
% 27.84/4.00  
% 27.84/4.00  ------ Superposition Options
% 27.84/4.00  
% 27.84/4.00  --superposition_flag                    true
% 27.84/4.00  --sup_passive_queue_type                priority_queues
% 27.84/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.84/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.84/4.00  --demod_completeness_check              fast
% 27.84/4.00  --demod_use_ground                      true
% 27.84/4.00  --sup_to_prop_solver                    passive
% 27.84/4.00  --sup_prop_simpl_new                    true
% 27.84/4.00  --sup_prop_simpl_given                  true
% 27.84/4.00  --sup_fun_splitting                     true
% 27.84/4.00  --sup_smt_interval                      50000
% 27.84/4.00  
% 27.84/4.00  ------ Superposition Simplification Setup
% 27.84/4.00  
% 27.84/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.84/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.84/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.84/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.84/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.84/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.84/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.84/4.00  --sup_immed_triv                        [TrivRules]
% 27.84/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/4.00  --sup_immed_bw_main                     []
% 27.84/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.84/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.84/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/4.00  --sup_input_bw                          []
% 27.84/4.00  
% 27.84/4.00  ------ Combination Options
% 27.84/4.00  
% 27.84/4.00  --comb_res_mult                         3
% 27.84/4.00  --comb_sup_mult                         2
% 27.84/4.00  --comb_inst_mult                        10
% 27.84/4.00  
% 27.84/4.00  ------ Debug Options
% 27.84/4.00  
% 27.84/4.00  --dbg_backtrace                         false
% 27.84/4.00  --dbg_dump_prop_clauses                 false
% 27.84/4.00  --dbg_dump_prop_clauses_file            -
% 27.84/4.00  --dbg_out_stat                          false
% 27.84/4.00  ------ Parsing...
% 27.84/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.84/4.00  ------ Proving...
% 27.84/4.00  ------ Problem Properties 
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  clauses                                 17
% 27.84/4.00  conjectures                             3
% 27.84/4.00  EPR                                     4
% 27.84/4.00  Horn                                    14
% 27.84/4.00  unary                                   9
% 27.84/4.00  binary                                  7
% 27.84/4.00  lits                                    26
% 27.84/4.00  lits eq                                 10
% 27.84/4.00  fd_pure                                 0
% 27.84/4.00  fd_pseudo                               0
% 27.84/4.00  fd_cond                                 0
% 27.84/4.00  fd_pseudo_cond                          0
% 27.84/4.00  AC symbols                              0
% 27.84/4.00  
% 27.84/4.00  ------ Schedule dynamic 5 is on 
% 27.84/4.00  
% 27.84/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  ------ 
% 27.84/4.00  Current options:
% 27.84/4.00  ------ 
% 27.84/4.00  
% 27.84/4.00  ------ Input Options
% 27.84/4.00  
% 27.84/4.00  --out_options                           all
% 27.84/4.00  --tptp_safe_out                         true
% 27.84/4.00  --problem_path                          ""
% 27.84/4.00  --include_path                          ""
% 27.84/4.00  --clausifier                            res/vclausify_rel
% 27.84/4.00  --clausifier_options                    ""
% 27.84/4.00  --stdin                                 false
% 27.84/4.00  --stats_out                             all
% 27.84/4.00  
% 27.84/4.00  ------ General Options
% 27.84/4.00  
% 27.84/4.00  --fof                                   false
% 27.84/4.00  --time_out_real                         305.
% 27.84/4.00  --time_out_virtual                      -1.
% 27.84/4.00  --symbol_type_check                     false
% 27.84/4.00  --clausify_out                          false
% 27.84/4.00  --sig_cnt_out                           false
% 27.84/4.00  --trig_cnt_out                          false
% 27.84/4.00  --trig_cnt_out_tolerance                1.
% 27.84/4.00  --trig_cnt_out_sk_spl                   false
% 27.84/4.00  --abstr_cl_out                          false
% 27.84/4.00  
% 27.84/4.00  ------ Global Options
% 27.84/4.00  
% 27.84/4.00  --schedule                              default
% 27.84/4.00  --add_important_lit                     false
% 27.84/4.00  --prop_solver_per_cl                    1000
% 27.84/4.00  --min_unsat_core                        false
% 27.84/4.00  --soft_assumptions                      false
% 27.84/4.00  --soft_lemma_size                       3
% 27.84/4.00  --prop_impl_unit_size                   0
% 27.84/4.00  --prop_impl_unit                        []
% 27.84/4.00  --share_sel_clauses                     true
% 27.84/4.00  --reset_solvers                         false
% 27.84/4.00  --bc_imp_inh                            [conj_cone]
% 27.84/4.00  --conj_cone_tolerance                   3.
% 27.84/4.00  --extra_neg_conj                        none
% 27.84/4.00  --large_theory_mode                     true
% 27.84/4.00  --prolific_symb_bound                   200
% 27.84/4.00  --lt_threshold                          2000
% 27.84/4.00  --clause_weak_htbl                      true
% 27.84/4.00  --gc_record_bc_elim                     false
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing Options
% 27.84/4.00  
% 27.84/4.00  --preprocessing_flag                    true
% 27.84/4.00  --time_out_prep_mult                    0.1
% 27.84/4.00  --splitting_mode                        input
% 27.84/4.00  --splitting_grd                         true
% 27.84/4.00  --splitting_cvd                         false
% 27.84/4.00  --splitting_cvd_svl                     false
% 27.84/4.00  --splitting_nvd                         32
% 27.84/4.00  --sub_typing                            true
% 27.84/4.00  --prep_gs_sim                           true
% 27.84/4.00  --prep_unflatten                        true
% 27.84/4.00  --prep_res_sim                          true
% 27.84/4.00  --prep_upred                            true
% 27.84/4.00  --prep_sem_filter                       exhaustive
% 27.84/4.00  --prep_sem_filter_out                   false
% 27.84/4.00  --pred_elim                             true
% 27.84/4.00  --res_sim_input                         true
% 27.84/4.00  --eq_ax_congr_red                       true
% 27.84/4.00  --pure_diseq_elim                       true
% 27.84/4.00  --brand_transform                       false
% 27.84/4.00  --non_eq_to_eq                          false
% 27.84/4.00  --prep_def_merge                        true
% 27.84/4.00  --prep_def_merge_prop_impl              false
% 27.84/4.00  --prep_def_merge_mbd                    true
% 27.84/4.00  --prep_def_merge_tr_red                 false
% 27.84/4.00  --prep_def_merge_tr_cl                  false
% 27.84/4.00  --smt_preprocessing                     true
% 27.84/4.00  --smt_ac_axioms                         fast
% 27.84/4.00  --preprocessed_out                      false
% 27.84/4.00  --preprocessed_stats                    false
% 27.84/4.00  
% 27.84/4.00  ------ Abstraction refinement Options
% 27.84/4.00  
% 27.84/4.00  --abstr_ref                             []
% 27.84/4.00  --abstr_ref_prep                        false
% 27.84/4.00  --abstr_ref_until_sat                   false
% 27.84/4.00  --abstr_ref_sig_restrict                funpre
% 27.84/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.84/4.00  --abstr_ref_under                       []
% 27.84/4.00  
% 27.84/4.00  ------ SAT Options
% 27.84/4.00  
% 27.84/4.00  --sat_mode                              false
% 27.84/4.00  --sat_fm_restart_options                ""
% 27.84/4.00  --sat_gr_def                            false
% 27.84/4.00  --sat_epr_types                         true
% 27.84/4.00  --sat_non_cyclic_types                  false
% 27.84/4.00  --sat_finite_models                     false
% 27.84/4.00  --sat_fm_lemmas                         false
% 27.84/4.00  --sat_fm_prep                           false
% 27.84/4.00  --sat_fm_uc_incr                        true
% 27.84/4.00  --sat_out_model                         small
% 27.84/4.00  --sat_out_clauses                       false
% 27.84/4.00  
% 27.84/4.00  ------ QBF Options
% 27.84/4.00  
% 27.84/4.00  --qbf_mode                              false
% 27.84/4.00  --qbf_elim_univ                         false
% 27.84/4.00  --qbf_dom_inst                          none
% 27.84/4.00  --qbf_dom_pre_inst                      false
% 27.84/4.00  --qbf_sk_in                             false
% 27.84/4.00  --qbf_pred_elim                         true
% 27.84/4.00  --qbf_split                             512
% 27.84/4.00  
% 27.84/4.00  ------ BMC1 Options
% 27.84/4.00  
% 27.84/4.00  --bmc1_incremental                      false
% 27.84/4.00  --bmc1_axioms                           reachable_all
% 27.84/4.00  --bmc1_min_bound                        0
% 27.84/4.00  --bmc1_max_bound                        -1
% 27.84/4.00  --bmc1_max_bound_default                -1
% 27.84/4.00  --bmc1_symbol_reachability              true
% 27.84/4.00  --bmc1_property_lemmas                  false
% 27.84/4.00  --bmc1_k_induction                      false
% 27.84/4.00  --bmc1_non_equiv_states                 false
% 27.84/4.00  --bmc1_deadlock                         false
% 27.84/4.00  --bmc1_ucm                              false
% 27.84/4.00  --bmc1_add_unsat_core                   none
% 27.84/4.00  --bmc1_unsat_core_children              false
% 27.84/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.84/4.00  --bmc1_out_stat                         full
% 27.84/4.00  --bmc1_ground_init                      false
% 27.84/4.00  --bmc1_pre_inst_next_state              false
% 27.84/4.00  --bmc1_pre_inst_state                   false
% 27.84/4.00  --bmc1_pre_inst_reach_state             false
% 27.84/4.00  --bmc1_out_unsat_core                   false
% 27.84/4.00  --bmc1_aig_witness_out                  false
% 27.84/4.00  --bmc1_verbose                          false
% 27.84/4.00  --bmc1_dump_clauses_tptp                false
% 27.84/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.84/4.00  --bmc1_dump_file                        -
% 27.84/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.84/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.84/4.00  --bmc1_ucm_extend_mode                  1
% 27.84/4.00  --bmc1_ucm_init_mode                    2
% 27.84/4.00  --bmc1_ucm_cone_mode                    none
% 27.84/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.84/4.00  --bmc1_ucm_relax_model                  4
% 27.84/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.84/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.84/4.00  --bmc1_ucm_layered_model                none
% 27.84/4.00  --bmc1_ucm_max_lemma_size               10
% 27.84/4.00  
% 27.84/4.00  ------ AIG Options
% 27.84/4.00  
% 27.84/4.00  --aig_mode                              false
% 27.84/4.00  
% 27.84/4.00  ------ Instantiation Options
% 27.84/4.00  
% 27.84/4.00  --instantiation_flag                    true
% 27.84/4.00  --inst_sos_flag                         true
% 27.84/4.00  --inst_sos_phase                        true
% 27.84/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.84/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.84/4.00  --inst_lit_sel_side                     none
% 27.84/4.00  --inst_solver_per_active                1400
% 27.84/4.00  --inst_solver_calls_frac                1.
% 27.84/4.00  --inst_passive_queue_type               priority_queues
% 27.84/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.84/4.00  --inst_passive_queues_freq              [25;2]
% 27.84/4.00  --inst_dismatching                      true
% 27.84/4.00  --inst_eager_unprocessed_to_passive     true
% 27.84/4.00  --inst_prop_sim_given                   true
% 27.84/4.00  --inst_prop_sim_new                     false
% 27.84/4.00  --inst_subs_new                         false
% 27.84/4.00  --inst_eq_res_simp                      false
% 27.84/4.00  --inst_subs_given                       false
% 27.84/4.00  --inst_orphan_elimination               true
% 27.84/4.00  --inst_learning_loop_flag               true
% 27.84/4.00  --inst_learning_start                   3000
% 27.84/4.00  --inst_learning_factor                  2
% 27.84/4.00  --inst_start_prop_sim_after_learn       3
% 27.84/4.00  --inst_sel_renew                        solver
% 27.84/4.00  --inst_lit_activity_flag                true
% 27.84/4.00  --inst_restr_to_given                   false
% 27.84/4.00  --inst_activity_threshold               500
% 27.84/4.00  --inst_out_proof                        true
% 27.84/4.00  
% 27.84/4.00  ------ Resolution Options
% 27.84/4.00  
% 27.84/4.00  --resolution_flag                       false
% 27.84/4.00  --res_lit_sel                           adaptive
% 27.84/4.00  --res_lit_sel_side                      none
% 27.84/4.00  --res_ordering                          kbo
% 27.84/4.00  --res_to_prop_solver                    active
% 27.84/4.00  --res_prop_simpl_new                    false
% 27.84/4.00  --res_prop_simpl_given                  true
% 27.84/4.00  --res_passive_queue_type                priority_queues
% 27.84/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.84/4.00  --res_passive_queues_freq               [15;5]
% 27.84/4.00  --res_forward_subs                      full
% 27.84/4.00  --res_backward_subs                     full
% 27.84/4.00  --res_forward_subs_resolution           true
% 27.84/4.00  --res_backward_subs_resolution          true
% 27.84/4.00  --res_orphan_elimination                true
% 27.84/4.00  --res_time_limit                        2.
% 27.84/4.00  --res_out_proof                         true
% 27.84/4.00  
% 27.84/4.00  ------ Superposition Options
% 27.84/4.00  
% 27.84/4.00  --superposition_flag                    true
% 27.84/4.00  --sup_passive_queue_type                priority_queues
% 27.84/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.84/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.84/4.00  --demod_completeness_check              fast
% 27.84/4.00  --demod_use_ground                      true
% 27.84/4.00  --sup_to_prop_solver                    passive
% 27.84/4.00  --sup_prop_simpl_new                    true
% 27.84/4.00  --sup_prop_simpl_given                  true
% 27.84/4.00  --sup_fun_splitting                     true
% 27.84/4.00  --sup_smt_interval                      50000
% 27.84/4.00  
% 27.84/4.00  ------ Superposition Simplification Setup
% 27.84/4.00  
% 27.84/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.84/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.84/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.84/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.84/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.84/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.84/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.84/4.00  --sup_immed_triv                        [TrivRules]
% 27.84/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/4.00  --sup_immed_bw_main                     []
% 27.84/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.84/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.84/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.84/4.00  --sup_input_bw                          []
% 27.84/4.00  
% 27.84/4.00  ------ Combination Options
% 27.84/4.00  
% 27.84/4.00  --comb_res_mult                         3
% 27.84/4.00  --comb_sup_mult                         2
% 27.84/4.00  --comb_inst_mult                        10
% 27.84/4.00  
% 27.84/4.00  ------ Debug Options
% 27.84/4.00  
% 27.84/4.00  --dbg_backtrace                         false
% 27.84/4.00  --dbg_dump_prop_clauses                 false
% 27.84/4.00  --dbg_dump_prop_clauses_file            -
% 27.84/4.00  --dbg_out_stat                          false
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  ------ Proving...
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  % SZS status Theorem for theBenchmark.p
% 27.84/4.00  
% 27.84/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.84/4.00  
% 27.84/4.00  fof(f1,axiom,(
% 27.84/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f30,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f1])).
% 27.84/4.00  
% 27.84/4.00  fof(f5,axiom,(
% 27.84/4.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f21,plain,(
% 27.84/4.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 27.84/4.00    inference(ennf_transformation,[],[f5])).
% 27.84/4.00  
% 27.84/4.00  fof(f36,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f21])).
% 27.84/4.00  
% 27.84/4.00  fof(f6,axiom,(
% 27.84/4.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f37,plain,(
% 27.84/4.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f6])).
% 27.84/4.00  
% 27.84/4.00  fof(f16,conjecture,(
% 27.84/4.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f17,negated_conjecture,(
% 27.84/4.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 27.84/4.00    inference(negated_conjecture,[],[f16])).
% 27.84/4.00  
% 27.84/4.00  fof(f22,plain,(
% 27.84/4.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 27.84/4.00    inference(ennf_transformation,[],[f17])).
% 27.84/4.00  
% 27.84/4.00  fof(f23,plain,(
% 27.84/4.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 27.84/4.00    inference(flattening,[],[f22])).
% 27.84/4.00  
% 27.84/4.00  fof(f28,plain,(
% 27.84/4.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 27.84/4.00    introduced(choice_axiom,[])).
% 27.84/4.00  
% 27.84/4.00  fof(f29,plain,(
% 27.84/4.00    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 27.84/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f28])).
% 27.84/4.00  
% 27.84/4.00  fof(f51,plain,(
% 27.84/4.00    r1_xboole_0(sK3,sK2)),
% 27.84/4.00    inference(cnf_transformation,[],[f29])).
% 27.84/4.00  
% 27.84/4.00  fof(f10,axiom,(
% 27.84/4.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f26,plain,(
% 27.84/4.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 27.84/4.00    inference(nnf_transformation,[],[f10])).
% 27.84/4.00  
% 27.84/4.00  fof(f41,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f26])).
% 27.84/4.00  
% 27.84/4.00  fof(f8,axiom,(
% 27.84/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f39,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f8])).
% 27.84/4.00  
% 27.84/4.00  fof(f9,axiom,(
% 27.84/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f40,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.84/4.00    inference(cnf_transformation,[],[f9])).
% 27.84/4.00  
% 27.84/4.00  fof(f57,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.84/4.00    inference(definition_unfolding,[],[f39,f40])).
% 27.84/4.00  
% 27.84/4.00  fof(f7,axiom,(
% 27.84/4.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f38,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f7])).
% 27.84/4.00  
% 27.84/4.00  fof(f2,axiom,(
% 27.84/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f31,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f2])).
% 27.84/4.00  
% 27.84/4.00  fof(f56,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 27.84/4.00    inference(definition_unfolding,[],[f31,f40,f40])).
% 27.84/4.00  
% 27.84/4.00  fof(f49,plain,(
% 27.84/4.00    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 27.84/4.00    inference(cnf_transformation,[],[f29])).
% 27.84/4.00  
% 27.84/4.00  fof(f11,axiom,(
% 27.84/4.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f43,plain,(
% 27.84/4.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f11])).
% 27.84/4.00  
% 27.84/4.00  fof(f12,axiom,(
% 27.84/4.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f44,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f12])).
% 27.84/4.00  
% 27.84/4.00  fof(f13,axiom,(
% 27.84/4.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f45,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f13])).
% 27.84/4.00  
% 27.84/4.00  fof(f14,axiom,(
% 27.84/4.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f46,plain,(
% 27.84/4.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f14])).
% 27.84/4.00  
% 27.84/4.00  fof(f53,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 27.84/4.00    inference(definition_unfolding,[],[f45,f46])).
% 27.84/4.00  
% 27.84/4.00  fof(f54,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 27.84/4.00    inference(definition_unfolding,[],[f44,f53])).
% 27.84/4.00  
% 27.84/4.00  fof(f55,plain,(
% 27.84/4.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 27.84/4.00    inference(definition_unfolding,[],[f43,f54])).
% 27.84/4.00  
% 27.84/4.00  fof(f60,plain,(
% 27.84/4.00    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 27.84/4.00    inference(definition_unfolding,[],[f49,f40,f55])).
% 27.84/4.00  
% 27.84/4.00  fof(f42,plain,(
% 27.84/4.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 27.84/4.00    inference(cnf_transformation,[],[f26])).
% 27.84/4.00  
% 27.84/4.00  fof(f50,plain,(
% 27.84/4.00    r2_hidden(sK4,sK3)),
% 27.84/4.00    inference(cnf_transformation,[],[f29])).
% 27.84/4.00  
% 27.84/4.00  fof(f4,axiom,(
% 27.84/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f18,plain,(
% 27.84/4.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 27.84/4.00    inference(rectify,[],[f4])).
% 27.84/4.00  
% 27.84/4.00  fof(f20,plain,(
% 27.84/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 27.84/4.00    inference(ennf_transformation,[],[f18])).
% 27.84/4.00  
% 27.84/4.00  fof(f24,plain,(
% 27.84/4.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 27.84/4.00    introduced(choice_axiom,[])).
% 27.84/4.00  
% 27.84/4.00  fof(f25,plain,(
% 27.84/4.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 27.84/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f24])).
% 27.84/4.00  
% 27.84/4.00  fof(f35,plain,(
% 27.84/4.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f25])).
% 27.84/4.00  
% 27.84/4.00  fof(f15,axiom,(
% 27.84/4.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f27,plain,(
% 27.84/4.00    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 27.84/4.00    inference(nnf_transformation,[],[f15])).
% 27.84/4.00  
% 27.84/4.00  fof(f48,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f27])).
% 27.84/4.00  
% 27.84/4.00  fof(f58,plain,(
% 27.84/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 27.84/4.00    inference(definition_unfolding,[],[f48,f55])).
% 27.84/4.00  
% 27.84/4.00  fof(f3,axiom,(
% 27.84/4.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 27.84/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.84/4.00  
% 27.84/4.00  fof(f19,plain,(
% 27.84/4.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 27.84/4.00    inference(ennf_transformation,[],[f3])).
% 27.84/4.00  
% 27.84/4.00  fof(f32,plain,(
% 27.84/4.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 27.84/4.00    inference(cnf_transformation,[],[f19])).
% 27.84/4.00  
% 27.84/4.00  fof(f52,plain,(
% 27.84/4.00    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 27.84/4.00    inference(cnf_transformation,[],[f29])).
% 27.84/4.00  
% 27.84/4.00  cnf(c_0,plain,
% 27.84/4.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f30]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6,plain,
% 27.84/4.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 27.84/4.00      inference(cnf_transformation,[],[f36]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7,plain,
% 27.84/4.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f37]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_203,plain,
% 27.84/4.00      ( X0 != X1 | k4_xboole_0(X0,X2) != X3 | k2_xboole_0(X3,X1) = X1 ),
% 27.84/4.00      inference(resolution_lifted,[status(thm)],[c_6,c_7]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_204,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 27.84/4.00      inference(unflattening,[status(thm)],[c_203]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1003,plain,
% 27.84/4.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15,negated_conjecture,
% 27.84/4.00      ( r1_xboole_0(sK3,sK2) ),
% 27.84/4.00      inference(cnf_transformation,[],[f51]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_629,plain,
% 27.84/4.00      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11,plain,
% 27.84/4.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 27.84/4.00      inference(cnf_transformation,[],[f41]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_633,plain,
% 27.84/4.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1527,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,sK2) = sK3 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_629,c_633]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(cnf_transformation,[],[f57]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1531,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK3,sK2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1527,c_9]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1537,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) = sK3 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1531,c_1527]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(cnf_transformation,[],[f38]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1632,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK3),X0)) = k4_xboole_0(sK3,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1537,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1911,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1003,c_1632]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1928,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) = sK3 ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_1911,c_1537]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1929,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK3,X0))) = sK3 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1928,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_2168,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(X0,sK3))) = sK3 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_1929]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_2996,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_2168,c_9]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.84/4.00      inference(cnf_transformation,[],[f56]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1082,plain,
% 27.84/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1,c_1003]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3017,plain,
% 27.84/4.00      ( k2_xboole_0(k2_xboole_0(X0,sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))) = k2_xboole_0(X0,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_2996,c_1082]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3018,plain,
% 27.84/4.00      ( k2_xboole_0(k2_xboole_0(X0,sK3),sK3) = k2_xboole_0(X0,sK3) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_3017,c_1537]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1208,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1436,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1208,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1448,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_1436,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17,negated_conjecture,
% 27.84/4.00      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 27.84/4.00      inference(cnf_transformation,[],[f60]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_209,plain,
% 27.84/4.00      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X0
% 27.84/4.00      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != X1
% 27.84/4.00      | k2_xboole_0(X1,X0) = X0 ),
% 27.84/4.00      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_210,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 27.84/4.00      inference(unflattening,[status(thm)],[c_209]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1197,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_12676,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_210,c_1197]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13988,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_12676,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14041,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))) = k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_13988,c_8,c_210]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41392,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))) = k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1448,c_14041]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41144,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_210,c_1448]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1083,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1,c_204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_43363,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_41144,c_1083]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1189,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7523,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1189,c_204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7605,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_7523,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_45016,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_43363,c_7605]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10,plain,
% 27.84/4.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 27.84/4.00      inference(cnf_transformation,[],[f42]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_634,plain,
% 27.84/4.00      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_43360,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) != sK2
% 27.84/4.00      | r1_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_41144,c_634]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_16,negated_conjecture,
% 27.84/4.00      ( r2_hidden(sK4,sK3) ),
% 27.84/4.00      inference(cnf_transformation,[],[f50]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3,plain,
% 27.84/4.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 27.84/4.00      inference(cnf_transformation,[],[f35]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_670,plain,
% 27.84/4.00      ( ~ r2_hidden(X0,sK2)
% 27.84/4.00      | ~ r2_hidden(X0,sK3)
% 27.84/4.00      | ~ r1_xboole_0(sK3,sK2) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_3]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_672,plain,
% 27.84/4.00      ( ~ r2_hidden(sK4,sK2)
% 27.84/4.00      | ~ r2_hidden(sK4,sK3)
% 27.84/4.00      | ~ r1_xboole_0(sK3,sK2) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_670]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_12,plain,
% 27.84/4.00      ( r2_hidden(X0,X1)
% 27.84/4.00      | k4_xboole_0(X1,k3_enumset1(X0,X0,X0,X0,X0)) = X1 ),
% 27.84/4.00      inference(cnf_transformation,[],[f58]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_5012,plain,
% 27.84/4.00      ( r2_hidden(X0,sK2)
% 27.84/4.00      | k4_xboole_0(sK2,k3_enumset1(X0,X0,X0,X0,X0)) = sK2 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_12]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_5014,plain,
% 27.84/4.00      ( r2_hidden(sK4,sK2)
% 27.84/4.00      | k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK2 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_5012]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_44681,plain,
% 27.84/4.00      ( r1_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = iProver_top ),
% 27.84/4.00      inference(global_propositional_subsumption,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_43360,c_16,c_15,c_672,c_5014]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_44686,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = sK2 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_44681,c_633]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_45027,plain,
% 27.84/4.00      ( k2_xboole_0(sK2,k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_45016,c_44686]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_45028,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = sK2 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_45027,c_1003]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_48435,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = sK2 ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_41392,c_41392,c_45028]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7522,plain,
% 27.84/4.00      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1189,c_1003]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7606,plain,
% 27.84/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_7522,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_2,plain,
% 27.84/4.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 27.84/4.00      inference(cnf_transformation,[],[f32]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_638,plain,
% 27.84/4.00      ( r1_xboole_0(X0,X1) != iProver_top
% 27.84/4.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 27.84/4.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6276,plain,
% 27.84/4.00      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_629,c_638]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6867,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6276,c_633]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6994,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6867,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10389,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK3),X1))) = k4_xboole_0(sK2,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_7606,c_6994]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10412,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK3),X1))) = sK2 ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_10389,c_6867]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10792,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,sK3)))) = sK2 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_10412]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_16582,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK2,sK2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_10792,c_9]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1532,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1527,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1756,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK3,sK2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1003,c_1532]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1773,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK2,X0)) = sK3 ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_1756,c_1527]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_2197,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK2,X0)) = k4_xboole_0(sK2,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1773,c_1083]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_2838,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_2197,c_1082]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1535,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK2,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1527,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_2839,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_2838,c_1535]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3597,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK3),X0)) = k4_xboole_0(k4_xboole_0(sK3,sK3),X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_2839,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_2184,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK3,X0)),k4_xboole_0(sK3,sK3)) = k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1929,c_1082]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1195,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_2186,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_2184,c_1195]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3616,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK3),X0)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_3597,c_8,c_2186]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_5063,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_204,c_3616]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14408,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1003,c_14041]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9982,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,sK2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_210,c_7605]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10482,plain,
% 27.84/4.00      ( k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_9982,c_7606]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7515,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK2),X0)) = k4_xboole_0(k4_xboole_0(sK2,sK2),X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6867,c_1189]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7612,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK3,sK3),X0) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_7515,c_1527,c_2186,c_5063]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_12821,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK3,sK3)))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1197,c_7612]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1429,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1452,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1429,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1453,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1452,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8616,plain,
% 27.84/4.00      ( k2_xboole_0(X0,k4_xboole_0(sK3,sK3)) = X0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_7612,c_1082]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_12836,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_12821,c_8,c_1453,c_8616]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13205,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_10482,c_12836]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14474,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_14408,c_13205]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1432,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_9,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1450,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1432,c_8,c_204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7507,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1,c_1189]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14475,plain,
% 27.84/4.00      ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_14474,c_1003,c_1450,c_7507]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_16605,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_16582,c_5063,c_6867,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1336,plain,
% 27.84/4.00      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = X0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_1082]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1338,plain,
% 27.84/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = X0 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1336,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_18619,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_10482,c_1338]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14008,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))) = k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_12676,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1194,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_1003]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9580,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_210,c_1194]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13239,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_9580,c_12836]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14019,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_14008,c_13239]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14020,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_14019,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1444,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1208,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1445,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_1444,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14021,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_14020,c_1445]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14022,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_14021,c_210]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13264,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK3,sK3)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_12836,c_1197]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13290,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK3,sK3)) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_13264,c_9]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_16968,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(sK1,sK1)) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_13290,c_13290,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17026,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,sK1)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_14022,c_16968]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17103,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_17026,c_16968]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17104,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_17103,c_14022,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_18771,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_18619,c_17104]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_48436,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 27.84/4.00      inference(demodulation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_48435,c_1208,c_1448,c_16605,c_18771]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_48465,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_48436,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_49880,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(k4_xboole_0(sK2,X0),X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_48465,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1191,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1200,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1191,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_49976,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = k4_xboole_0(sK2,k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_49880,c_8,c_1200]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7377,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k4_xboole_0(k4_xboole_0(sK2,X0),X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6994,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7393,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK3,X0),X1)) = k4_xboole_0(sK2,k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_7377,c_8,c_1200]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_38514,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK3,X1))) = k4_xboole_0(sK2,k2_xboole_0(X1,X0)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_7393]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10325,plain,
% 27.84/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X0)))) = X0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_7606]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_18000,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X2)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_9580,c_1200]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32324,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_10325,c_18000]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32435,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_32324,c_9580]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11129,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_1195]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64194,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))),k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_32435,c_11129]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_36285,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_32435,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_36333,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X2,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_36285,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41246,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))),X1)) = k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_12676,c_1448]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15023,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_13239,c_13239,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15046,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1)) = k4_xboole_0(k4_xboole_0(sK1,sK1),X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_15023,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13201,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_12836]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15077,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_15046,c_8,c_13201]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15078,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X1)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_15077,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41515,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))),X1)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_41246,c_15078]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1198,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1199,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1198,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1210,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1223,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_1210,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_26698,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1199,c_1223]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41516,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),X1))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_41515,c_8,c_26698]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41517,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X1))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_41516,c_210]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41177,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k4_xboole_0(X0,X0),X1)) = k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1208,c_1448]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41181,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1,c_1448]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41584,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_41181,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41585,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_41584,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41593,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_41177,c_41585]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1217,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1218,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_1217,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1219,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1218,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_20952,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1003,c_1219]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41594,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,X0) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_41593,c_8,c_20952]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41896,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_41594,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41774,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_41594]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17964,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X1))) = k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X1)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_210,c_1200]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19362,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17964,c_1189]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42401,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X1)),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_41774,c_19362]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42406,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X1)),X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)),X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_41774,c_1189]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_9981,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_204,c_7605]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42519,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X1)),X2)) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_42406,c_8,c_9981]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42520,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X1)),X2)) = k4_xboole_0(X1,X1) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_42519,c_20952]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42526,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X1)) = k4_xboole_0(X0,X0) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_42401,c_42520]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41865,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(X0,X1)))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_41594,c_1197]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41875,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,X0),X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_41594,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41174,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1199,c_1448]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1214,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1220,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_1214,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_23835,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_1220]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15760,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1199,c_1197]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_24113,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_23835,c_15760]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_24114,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_24113,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41596,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_41174,c_24114]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42023,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,X0) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_41875,c_8,c_20952,c_41596]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42034,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_41865,c_41594,c_42023]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15732,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1199,c_13201]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13396,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(sK3,sK3)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_13201,c_1197]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13416,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_13396,c_13290]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15785,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_15732,c_13416,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42035,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_42034,c_15785]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42527,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK1,sK1),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(X1,X1) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_42526,c_42035]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42528,plain,
% 27.84/4.00      ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
% 27.84/4.00      inference(splitting,
% 27.84/4.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 27.84/4.00                [c_42527]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42546,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X0,X1))) = sP0_iProver_split ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_41896,c_41896,c_42528]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14107,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k2_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_14022]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15117,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k2_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_14107,c_14107,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15198,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_210,c_15117]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17200,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1003,c_15198]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_36854,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK1)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17200,c_19362]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17228,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_15198,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11132,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_210,c_1195]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11627,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_11132,c_1189]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_20686,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17228,c_11627]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17329,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1003,c_17104]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_20689,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_20686,c_17329]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13243,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_11132,c_12836]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14669,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_13243,c_13243,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14696,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_14669,c_204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17347,plain,
% 27.84/4.00      ( k2_xboole_0(X0,k4_xboole_0(sK1,sK1)) = X0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17104,c_1003]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19343,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17964,c_1]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19371,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17964,c_11627]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17021,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,sK1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_13201,c_16968]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17109,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_17021,c_16968]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17110,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_17109,c_13201,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19376,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_19371,c_8,c_7507,c_17110]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19377,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_19376,c_14696]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19384,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_19343,c_19377]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19373,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17964,c_13201]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19374,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_19373,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19385,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK1)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_19384,c_19374]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_13240,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_9982,c_12836]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14500,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_13240,c_13240,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14513,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,sK2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_14500,c_1003]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19386,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_19385,c_7507,c_14513]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_20690,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 27.84/4.00      inference(demodulation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_20689,c_8,c_210,c_14696,c_17347,c_19386]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_37261,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK1)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_36854,c_20690]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17348,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK1,sK1),X0) = X0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17104,c_204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17630,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(k4_xboole_0(sK1,sK1),X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17200,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_16991,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,sK1)) = k4_xboole_0(k4_xboole_0(sK3,sK3),X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_7612,c_16968]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17151,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK3,sK3),X0) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_16991,c_16968]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17152,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_17151,c_7612,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17681,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_17630,c_17152]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19349,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_17964,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_19383,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2)))) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X2))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_19349,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_37262,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(demodulation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_37261,c_8,c_17348,c_17681,c_17964,c_19383]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42723,plain,
% 27.84/4.00      ( k4_xboole_0(sK1,sK1) = sP0_iProver_split ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_42546,c_37262]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_43611,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(X0,k3_enumset1(sK4,sK4,sK4,sK4,sK4)),X1))) = sP0_iProver_split ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_41517,c_41517,c_42723]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_43637,plain,
% 27.84/4.00      ( k4_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK2))) = sP0_iProver_split ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_9982,c_43611]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_43836,plain,
% 27.84/4.00      ( k4_xboole_0(sK1,k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sP0_iProver_split)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_43637,c_9]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_43891,plain,
% 27.84/4.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sP0_iProver_split)) = sP0_iProver_split ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_43836,c_43637]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_48475,plain,
% 27.84/4.00      ( k4_xboole_0(sK1,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK1,sK2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_48436,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1434,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1208,c_1083]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_28710,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1434,c_12836]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_28745,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_28710,c_1450,c_14475]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_45032,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = sP0_iProver_split ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_1450,c_28745,c_42528]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_45208,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,sK2) = sP0_iProver_split ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_10412,c_45032]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_48488,plain,
% 27.84/4.00      ( k4_xboole_0(sK1,sP0_iProver_split) = k4_xboole_0(sK1,sK2) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_48475,c_45208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64320,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X4,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),k4_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split))) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_64194,c_36333,c_43891,c_48488]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8608,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK3,sK3),X0) = X0 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_7612,c_1083]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1431,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1451,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1431,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_48999,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK3,sK3))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_8608,c_1451]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42721,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,sK3) = sP0_iProver_split ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_42546,c_13201]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_49311,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(sP0_iProver_split,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_48999,c_42721]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_45192,plain,
% 27.84/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = sP0_iProver_split ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_9,c_45032]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_46589,plain,
% 27.84/4.00      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_45192,c_204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_49312,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split)) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_49311,c_1208,c_46589]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64321,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X4,k4_xboole_0(X1,sP0_iProver_split))),k4_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(demodulation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_64320,c_43891,c_48488,c_49312]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64323,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = sP2_iProver_split(X0,X1) ),
% 27.84/4.00      inference(splitting,
% 27.84/4.00                [splitting(split),new_symbols(definition,[])],
% 27.84/4.00                [c_64321]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32317,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1338,c_18000]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_32439,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4)))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_32317,c_9580]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64260,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_11129,c_32439]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64266,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X3,k3_enumset1(sK4,sK4,sK4,sK4,sK4))),k4_xboole_0(X2,k4_xboole_0(X1,k3_enumset1(sK4,sK4,sK4,sK4,sK4))))))) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_64260,c_43891,c_48488,c_49312]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64325,plain,
% 27.84/4.00      ( sP2_iProver_split(X0,X1) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_64323,c_64266]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83401,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK3,X1))) = sP2_iProver_split(sK2,k2_xboole_0(X1,X0)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_38514,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83538,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_83401,c_6994]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1764,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,X0),X1)) = k4_xboole_0(k4_xboole_0(sK3,X0),X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1532,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1769,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,X0),X1)) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1764,c_8,c_1200]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_21570,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k4_xboole_0(sK3,k2_xboole_0(X1,X0)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_1769]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1754,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK3,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_1532]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1893,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,sK2),X1)) = k4_xboole_0(k4_xboole_0(sK3,X0),X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1754,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1898,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,sK2),X1)) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1893,c_8,c_1200]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_21811,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1898,c_1200]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_75864,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = sP2_iProver_split(sK3,k2_xboole_0(X1,X0)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_21570,c_21811,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_42571,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X0))) = sP0_iProver_split ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_42546]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_76036,plain,
% 27.84/4.00      ( sP2_iProver_split(sK3,k2_xboole_0(sK3,sK3)) = sP0_iProver_split ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_75864,c_42571]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1533,plain,
% 27.84/4.00      ( k2_xboole_0(sK3,sK3) = sK3 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1527,c_1003]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_76041,plain,
% 27.84/4.00      ( sP2_iProver_split(sK3,sK3) = sP0_iProver_split ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_76036,c_1533]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7369,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK2,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1003,c_6994]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7398,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = sK2 ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_7369,c_6867]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8686,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK3,X0),X1)) = k4_xboole_0(sK2,X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_7398,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_11330,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK3,X1))) = k4_xboole_0(sK2,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_8686]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_16660,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK3)))) = k4_xboole_0(sK2,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1,c_11330]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_71817,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(X0,sP2_iProver_split(X1,k4_xboole_0(X1,sK3)))) = sP2_iProver_split(sK2,X0) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_16660,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_71818,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(X0,sP2_iProver_split(X1,sP2_iProver_split(X1,sK3)))) = sP2_iProver_split(sK2,X0) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_71817,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83052,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(X0,sP2_iProver_split(sK3,sP0_iProver_split))) = sP2_iProver_split(sK2,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_76041,c_71818]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_34356,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k3_enumset1(sK4,sK4,sK4,sK4,sK4))) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_20690,c_1445]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_34704,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_34356,c_210,c_17329]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_41266,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,sK1)),X0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_34704,c_1448]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_78093,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(sP0_iProver_split,k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split)),k2_xboole_0(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split),X0)) = k4_xboole_0(k2_xboole_0(sP0_iProver_split,k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split)),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_41266,c_41266,c_42723,c_43891,c_48488]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8615,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK3,sK3)),X1)) = k4_xboole_0(k4_xboole_0(sK3,sK3),X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_7612,c_1189]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_8640,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK3,sK3)),X1)) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_8615,c_7612]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10871,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(sK3,sK3)))) = k4_xboole_0(sK3,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_8640]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_57206,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,sP0_iProver_split))) = sP0_iProver_split ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_10871,c_10871,c_42721]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_57293,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split)),k2_xboole_0(k4_xboole_0(X1,sP0_iProver_split),X2)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,sP0_iProver_split)),k2_xboole_0(X1,X2)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_57206,c_1448]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_78094,plain,
% 27.84/4.00      ( k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),k2_xboole_0(sP0_iProver_split,k2_xboole_0(sP2_iProver_split(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split),X0))) = sP2_iProver_split(k4_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) ),
% 27.84/4.00      inference(demodulation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_78093,c_41596,c_46589,c_57293,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17047,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_16968,c_7606]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_15221,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_15117,c_204]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_17076,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(sK1,sK1) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_17047,c_8,c_15221]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_71874,plain,
% 27.84/4.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sP2_iProver_split(X0,X1),X2))) = sP0_iProver_split ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_17076,c_17076,c_42723,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_78095,plain,
% 27.84/4.00      ( sP2_iProver_split(sP2_iProver_split(k3_enumset1(sK4,sK4,sK4,sK4,sK4),sP0_iProver_split),k2_xboole_0(k3_enumset1(sK4,sK4,sK4,sK4,sK4),X0)) = sP0_iProver_split ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_78094,c_64325,c_71874]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_2199,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK2,X0),X1)) = k4_xboole_0(sK3,X1) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1773,c_8]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3246,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK2,X1))) = k4_xboole_0(sK3,X0) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_2199]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10055,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,X1)),X2))) = k4_xboole_0(sK3,k4_xboole_0(sK2,X1)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_7605,c_3246]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_10060,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,X1)),X2))) = sK3 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_10055,c_1773]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_12486,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(sK2,X2))))) = sK3 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_10060]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64390,plain,
% 27.84/4.00      ( sP2_iProver_split(sK3,sP2_iProver_split(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(sK2,X2))))) = sK3 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_12486,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64391,plain,
% 27.84/4.00      ( sP2_iProver_split(sK3,sP2_iProver_split(X0,k2_xboole_0(X1,sP2_iProver_split(X0,k4_xboole_0(sK2,X2))))) = sK3 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_64390,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_64392,plain,
% 27.84/4.00      ( sP2_iProver_split(sK3,sP2_iProver_split(X0,k2_xboole_0(X1,sP2_iProver_split(X0,sP2_iProver_split(sK2,X2))))) = sK3 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_64391,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_78115,plain,
% 27.84/4.00      ( sP2_iProver_split(sK3,sP0_iProver_split) = sK3 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_78095,c_64392]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83067,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(X0,sK3)) = sP2_iProver_split(sK2,X0) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_83052,c_78115]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83640,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,X0) = k4_xboole_0(sK2,X0) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_83538,c_6994,c_83067]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_87875,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK1,X0),X1)) = sP2_iProver_split(sK2,k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_49976,c_83640]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_87906,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(sK3,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_3018,c_87875]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_6996,plain,
% 27.84/4.00      ( k2_xboole_0(sK2,sK2) = sK2 ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6867,c_1003]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_21747,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK2))) = k4_xboole_0(sK3,k2_xboole_0(X1,X0)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_1898]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_75919,plain,
% 27.84/4.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK2))) = sP2_iProver_split(sK3,k2_xboole_0(X1,X0)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_75864]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_76450,plain,
% 27.84/4.00      ( sP2_iProver_split(sK3,k2_xboole_0(X0,X1)) = k4_xboole_0(sK3,k2_xboole_0(X0,X1)) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_21747,c_75919]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_76553,plain,
% 27.84/4.00      ( sP2_iProver_split(sK3,k2_xboole_0(sK2,sK2)) = k4_xboole_0(sK3,sK2) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_6996,c_76450]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77200,plain,
% 27.84/4.00      ( sP2_iProver_split(sK3,sK2) = sK3 ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_76553,c_1527,c_6996]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_1767,plain,
% 27.84/4.00      ( k4_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1532,c_1208]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_66950,plain,
% 27.84/4.00      ( sP2_iProver_split(k2_xboole_0(sK2,X0),sP2_iProver_split(sK3,k4_xboole_0(sK3,X0))) = sP2_iProver_split(k2_xboole_0(sK2,X0),sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_1767,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_66951,plain,
% 27.84/4.00      ( sP2_iProver_split(k2_xboole_0(sK2,X0),sP2_iProver_split(sK3,sP2_iProver_split(sK3,X0))) = sP2_iProver_split(k2_xboole_0(sK2,X0),sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_66950,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77403,plain,
% 27.84/4.00      ( sP2_iProver_split(k2_xboole_0(sK2,sK2),sP2_iProver_split(sK3,sK3)) = sP2_iProver_split(k2_xboole_0(sK2,sK2),sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_77200,c_66951]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_77404,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,sP0_iProver_split) = sP2_iProver_split(sK2,sK3) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_77403,c_6996,c_76041]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_88197,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = sP2_iProver_split(sK2,sP0_iProver_split) ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_87906,c_1533,c_77404]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3011,plain,
% 27.84/4.00      ( k2_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)),k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_2996,c_1083]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3023,plain,
% 27.84/4.00      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,sK3) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_3011,c_1537]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83436,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(sK3,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK3)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_3023,c_83401]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83459,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_1533,c_83401]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_3648,plain,
% 27.84/4.00      ( k2_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,sK3) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_0,c_3023]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7371,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
% 27.84/4.00      inference(superposition,[status(thm)],[c_3648,c_6994]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_7396,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK2,X0) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_7371,c_6994]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83759,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
% 27.84/4.00      inference(light_normalisation,[status(thm)],[c_83459,c_7396]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83760,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,k2_xboole_0(sK3,X0)) = sP2_iProver_split(sK2,X0) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_83759,c_64325]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83794,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK3)) = sP2_iProver_split(sK2,sK3) ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_83436,c_83640,c_83760]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_83795,plain,
% 27.84/4.00      ( sP2_iProver_split(sK2,sP0_iProver_split) = sK2 ),
% 27.84/4.00      inference(light_normalisation,
% 27.84/4.00                [status(thm)],
% 27.84/4.00                [c_83794,c_1533,c_6867,c_77404]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_88198,plain,
% 27.84/4.00      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = sK2 ),
% 27.84/4.00      inference(demodulation,[status(thm)],[c_88197,c_48465,c_83795]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_723,plain,
% 27.84/4.00      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
% 27.84/4.00      | k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != sK2 ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_10]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_662,plain,
% 27.84/4.00      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
% 27.84/4.00      | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
% 27.84/4.00      inference(instantiation,[status(thm)],[c_2]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(c_14,negated_conjecture,
% 27.84/4.00      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 27.84/4.00      inference(cnf_transformation,[],[f52]) ).
% 27.84/4.00  
% 27.84/4.00  cnf(contradiction,plain,
% 27.84/4.00      ( $false ),
% 27.84/4.00      inference(minisat,[status(thm)],[c_88198,c_723,c_662,c_14]) ).
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.84/4.00  
% 27.84/4.00  ------                               Statistics
% 27.84/4.00  
% 27.84/4.00  ------ General
% 27.84/4.00  
% 27.84/4.00  abstr_ref_over_cycles:                  0
% 27.84/4.00  abstr_ref_under_cycles:                 0
% 27.84/4.00  gc_basic_clause_elim:                   0
% 27.84/4.00  forced_gc_time:                         0
% 27.84/4.00  parsing_time:                           0.011
% 27.84/4.00  unif_index_cands_time:                  0.
% 27.84/4.00  unif_index_add_time:                    0.
% 27.84/4.00  orderings_time:                         0.
% 27.84/4.00  out_proof_time:                         0.027
% 27.84/4.00  total_time:                             3.295
% 27.84/4.00  num_of_symbols:                         45
% 27.84/4.00  num_of_terms:                           159943
% 27.84/4.00  
% 27.84/4.00  ------ Preprocessing
% 27.84/4.00  
% 27.84/4.00  num_of_splits:                          0
% 27.84/4.00  num_of_split_atoms:                     3
% 27.84/4.00  num_of_reused_defs:                     2
% 27.84/4.00  num_eq_ax_congr_red:                    6
% 27.84/4.00  num_of_sem_filtered_clauses:            1
% 27.84/4.00  num_of_subtypes:                        0
% 27.84/4.00  monotx_restored_types:                  0
% 27.84/4.00  sat_num_of_epr_types:                   0
% 27.84/4.00  sat_num_of_non_cyclic_types:            0
% 27.84/4.00  sat_guarded_non_collapsed_types:        0
% 27.84/4.00  num_pure_diseq_elim:                    0
% 27.84/4.00  simp_replaced_by:                       0
% 27.84/4.00  res_preprocessed:                       84
% 27.84/4.00  prep_upred:                             0
% 27.84/4.00  prep_unflattend:                        4
% 27.84/4.00  smt_new_axioms:                         0
% 27.84/4.00  pred_elim_cands:                        2
% 27.84/4.00  pred_elim:                              1
% 27.84/4.00  pred_elim_cl:                           1
% 27.84/4.00  pred_elim_cycles:                       3
% 27.84/4.00  merged_defs:                            16
% 27.84/4.00  merged_defs_ncl:                        0
% 27.84/4.00  bin_hyper_res:                          16
% 27.84/4.00  prep_cycles:                            4
% 27.84/4.00  pred_elim_time:                         0.
% 27.84/4.00  splitting_time:                         0.
% 27.84/4.00  sem_filter_time:                        0.
% 27.84/4.00  monotx_time:                            0.001
% 27.84/4.00  subtype_inf_time:                       0.
% 27.84/4.00  
% 27.84/4.00  ------ Problem properties
% 27.84/4.00  
% 27.84/4.00  clauses:                                17
% 27.84/4.00  conjectures:                            3
% 27.84/4.00  epr:                                    4
% 27.84/4.00  horn:                                   14
% 27.84/4.00  ground:                                 4
% 27.84/4.00  unary:                                  9
% 27.84/4.00  binary:                                 7
% 27.84/4.00  lits:                                   26
% 27.84/4.00  lits_eq:                                10
% 27.84/4.00  fd_pure:                                0
% 27.84/4.00  fd_pseudo:                              0
% 27.84/4.00  fd_cond:                                0
% 27.84/4.00  fd_pseudo_cond:                         0
% 27.84/4.00  ac_symbols:                             0
% 27.84/4.00  
% 27.84/4.00  ------ Propositional Solver
% 27.84/4.00  
% 27.84/4.00  prop_solver_calls:                      32
% 27.84/4.00  prop_fast_solver_calls:                 900
% 27.84/4.00  smt_solver_calls:                       0
% 27.84/4.00  smt_fast_solver_calls:                  0
% 27.84/4.00  prop_num_of_clauses:                    30184
% 27.84/4.00  prop_preprocess_simplified:             29663
% 27.84/4.00  prop_fo_subsumed:                       3
% 27.84/4.00  prop_solver_time:                       0.
% 27.84/4.00  smt_solver_time:                        0.
% 27.84/4.00  smt_fast_solver_time:                   0.
% 27.84/4.00  prop_fast_solver_time:                  0.
% 27.84/4.00  prop_unsat_core_time:                   0.003
% 27.84/4.00  
% 27.84/4.00  ------ QBF
% 27.84/4.00  
% 27.84/4.00  qbf_q_res:                              0
% 27.84/4.00  qbf_num_tautologies:                    0
% 27.84/4.00  qbf_prep_cycles:                        0
% 27.84/4.00  
% 27.84/4.00  ------ BMC1
% 27.84/4.00  
% 27.84/4.00  bmc1_current_bound:                     -1
% 27.84/4.00  bmc1_last_solved_bound:                 -1
% 27.84/4.00  bmc1_unsat_core_size:                   -1
% 27.84/4.00  bmc1_unsat_core_parents_size:           -1
% 27.84/4.00  bmc1_merge_next_fun:                    0
% 27.84/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.84/4.00  
% 27.84/4.00  ------ Instantiation
% 27.84/4.00  
% 27.84/4.00  inst_num_of_clauses:                    4530
% 27.84/4.00  inst_num_in_passive:                    1752
% 27.84/4.00  inst_num_in_active:                     1683
% 27.84/4.00  inst_num_in_unprocessed:                1095
% 27.84/4.00  inst_num_of_loops:                      1890
% 27.84/4.00  inst_num_of_learning_restarts:          0
% 27.84/4.00  inst_num_moves_active_passive:          206
% 27.84/4.00  inst_lit_activity:                      0
% 27.84/4.00  inst_lit_activity_moves:                0
% 27.84/4.00  inst_num_tautologies:                   0
% 27.84/4.00  inst_num_prop_implied:                  0
% 27.84/4.00  inst_num_existing_simplified:           0
% 27.84/4.00  inst_num_eq_res_simplified:             0
% 27.84/4.00  inst_num_child_elim:                    0
% 27.84/4.00  inst_num_of_dismatching_blockings:      2354
% 27.84/4.00  inst_num_of_non_proper_insts:           4611
% 27.84/4.00  inst_num_of_duplicates:                 0
% 27.84/4.00  inst_inst_num_from_inst_to_res:         0
% 27.84/4.00  inst_dismatching_checking_time:         0.
% 27.84/4.00  
% 27.84/4.00  ------ Resolution
% 27.84/4.00  
% 27.84/4.00  res_num_of_clauses:                     0
% 27.84/4.00  res_num_in_passive:                     0
% 27.84/4.00  res_num_in_active:                      0
% 27.84/4.00  res_num_of_loops:                       88
% 27.84/4.00  res_forward_subset_subsumed:            222
% 27.84/4.00  res_backward_subset_subsumed:           0
% 27.84/4.00  res_forward_subsumed:                   0
% 27.84/4.00  res_backward_subsumed:                  0
% 27.84/4.00  res_forward_subsumption_resolution:     0
% 27.84/4.00  res_backward_subsumption_resolution:    0
% 27.84/4.00  res_clause_to_clause_subsumption:       66160
% 27.84/4.00  res_orphan_elimination:                 0
% 27.84/4.00  res_tautology_del:                      260
% 27.84/4.00  res_num_eq_res_simplified:              0
% 27.84/4.00  res_num_sel_changes:                    0
% 27.84/4.00  res_moves_from_active_to_pass:          0
% 27.84/4.00  
% 27.84/4.00  ------ Superposition
% 27.84/4.00  
% 27.84/4.00  sup_time_total:                         0.
% 27.84/4.00  sup_time_generating:                    0.
% 27.84/4.00  sup_time_sim_full:                      0.
% 27.84/4.00  sup_time_sim_immed:                     0.
% 27.84/4.00  
% 27.84/4.00  sup_num_of_clauses:                     7792
% 27.84/4.00  sup_num_in_active:                      308
% 27.84/4.00  sup_num_in_passive:                     7484
% 27.84/4.00  sup_num_of_loops:                       377
% 27.84/4.00  sup_fw_superposition:                   15013
% 27.84/4.00  sup_bw_superposition:                   13561
% 27.84/4.00  sup_immediate_simplified:               18025
% 27.84/4.00  sup_given_eliminated:                   11
% 27.84/4.00  comparisons_done:                       0
% 27.84/4.00  comparisons_avoided:                    0
% 27.84/4.00  
% 27.84/4.00  ------ Simplifications
% 27.84/4.00  
% 27.84/4.00  
% 27.84/4.00  sim_fw_subset_subsumed:                 60
% 27.84/4.00  sim_bw_subset_subsumed:                 13
% 27.84/4.00  sim_fw_subsumed:                        2311
% 27.84/4.00  sim_bw_subsumed:                        403
% 27.84/4.00  sim_fw_subsumption_res:                 0
% 27.84/4.00  sim_bw_subsumption_res:                 0
% 27.84/4.00  sim_tautology_del:                      0
% 27.84/4.00  sim_eq_tautology_del:                   4867
% 27.84/4.00  sim_eq_res_simp:                        55
% 27.84/4.00  sim_fw_demodulated:                     13870
% 27.84/4.00  sim_bw_demodulated:                     340
% 27.84/4.00  sim_light_normalised:                   7653
% 27.84/4.00  sim_joinable_taut:                      0
% 27.84/4.00  sim_joinable_simp:                      0
% 27.84/4.00  sim_ac_normalised:                      0
% 27.84/4.00  sim_smt_subsumption:                    0
% 27.84/4.00  
%------------------------------------------------------------------------------
