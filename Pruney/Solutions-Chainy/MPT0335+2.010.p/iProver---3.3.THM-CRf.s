%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:26 EST 2020

% Result     : Theorem 27.62s
% Output     : CNFRefutation 27.62s
% Verified   : 
% Statistics : Number of formulae       :  170 (3769 expanded)
%              Number of clauses        :  121 ( 902 expanded)
%              Number of leaves         :   14 (1115 expanded)
%              Depth                    :   32
%              Number of atoms          :  235 (5780 expanded)
%              Number of equality atoms :  176 (4245 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f33,f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).

fof(f40,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f39,f33,f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f31,f33,f33,f33,f33])).

fof(f38,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f41,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f41,f33,f43])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_121,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
    | sK3 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_122,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),sK0) ),
    inference(unflattening,[status(thm)],[c_121])).

cnf(c_369,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_122])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_510,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_369,c_12])).

cnf(c_690,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_510])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_372,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1148,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_690,c_372])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1248,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1148,c_7])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_370,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1147,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_370,c_372])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_767,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_1154,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_1147,c_767])).

cnf(c_1317,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK1) ),
    inference(superposition,[status(thm)],[c_1154,c_767])).

cnf(c_2250,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK1) ),
    inference(superposition,[status(thm)],[c_0,c_1317])).

cnf(c_1152,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1147,c_8])).

cnf(c_1155,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1152,c_1147])).

cnf(c_1232,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
    inference(superposition,[status(thm)],[c_1155,c_767])).

cnf(c_2266,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK1) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
    inference(light_normalisation,[status(thm)],[c_2250,c_1147,c_1232])).

cnf(c_2275,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_2266,c_0])).

cnf(c_1150,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_1147,c_7])).

cnf(c_2022,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0))))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) ),
    inference(superposition,[status(thm)],[c_1232,c_1150])).

cnf(c_2023,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2022,c_1154])).

cnf(c_2024,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_2023,c_767,c_1150])).

cnf(c_2025,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2024,c_1147])).

cnf(c_2279,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2275,c_1154,c_2025])).

cnf(c_3073,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1248,c_1248,c_2279])).

cnf(c_884,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_11939,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
    inference(superposition,[status(thm)],[c_0,c_884])).

cnf(c_12356,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_11939,c_8,c_767])).

cnf(c_868,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_892,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(light_normalisation,[status(thm)],[c_868,c_767])).

cnf(c_12357,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_12356,c_8,c_892])).

cnf(c_12734,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_12357])).

cnf(c_23619,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3073,c_12734])).

cnf(c_1343,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_1150,c_0])).

cnf(c_3552,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_0,c_1343])).

cnf(c_2766,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_2279,c_7])).

cnf(c_2775,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_2766,c_1150])).

cnf(c_4539,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))))) ),
    inference(superposition,[status(thm)],[c_3552,c_2775])).

cnf(c_3635,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1)))))) ),
    inference(superposition,[status(thm)],[c_7,c_3552])).

cnf(c_863,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_3662,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1)))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))))) ),
    inference(demodulation,[status(thm)],[c_3635,c_863])).

cnf(c_4605,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ),
    inference(demodulation,[status(thm)],[c_4539,c_767,c_3662])).

cnf(c_844,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_4936,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_1147,c_844])).

cnf(c_997,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_7,c_767])).

cnf(c_5827,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0)))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_1147,c_997])).

cnf(c_24122,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_23619,c_4605,c_4936,c_5827])).

cnf(c_1012,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_767,c_767])).

cnf(c_72293,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_24122,c_1012])).

cnf(c_12031,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2))) ),
    inference(superposition,[status(thm)],[c_884,c_884])).

cnf(c_1006,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_767,c_7])).

cnf(c_1018,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(light_normalisation,[status(thm)],[c_1006,c_863])).

cnf(c_1019,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(demodulation,[status(thm)],[c_1018,c_8,c_863])).

cnf(c_12747,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3) ),
    inference(superposition,[status(thm)],[c_1019,c_12357])).

cnf(c_12741,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),X3) ),
    inference(superposition,[status(thm)],[c_863,c_12357])).

cnf(c_12935,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X3) ),
    inference(light_normalisation,[status(thm)],[c_12741,c_863])).

cnf(c_13037,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2) ),
    inference(demodulation,[status(thm)],[c_12031,c_12747,c_12935])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13038,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(demodulation,[status(thm)],[c_13037,c_1,c_767])).

cnf(c_72635,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1012,c_13038])).

cnf(c_72589,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1012,c_1])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_373,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1146,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_373,c_372])).

cnf(c_72761,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_72589,c_1,c_1146])).

cnf(c_73302,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK1) ),
    inference(demodulation,[status(thm)],[c_72293,c_72635,c_72761])).

cnf(c_1243,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) ),
    inference(superposition,[status(thm)],[c_1148,c_8])).

cnf(c_1249,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1243,c_1148])).

cnf(c_2177,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1249,c_7])).

cnf(c_2483,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2177,c_8])).

cnf(c_2574,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1))) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_0,c_2483])).

cnf(c_4960,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2574,c_844])).

cnf(c_2487,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2483,c_2177])).

cnf(c_5170,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4960,c_2487])).

cnf(c_73303,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK1) ),
    inference(light_normalisation,[status(thm)],[c_73302,c_5170])).

cnf(c_883,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) ),
    inference(superposition,[status(thm)],[c_7,c_7])).

cnf(c_885,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_883,c_884])).

cnf(c_16989,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X2))) ),
    inference(superposition,[status(thm)],[c_885,c_997])).

cnf(c_8089,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1019,c_767])).

cnf(c_17010,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_16989,c_863,c_8089])).

cnf(c_17011,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_17010,c_1])).

cnf(c_25210,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_17011,c_13038])).

cnf(c_73304,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK1) ),
    inference(demodulation,[status(thm)],[c_73303,c_25210])).

cnf(c_1233,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1155,c_767])).

cnf(c_1235,plain,
    ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1233,c_1146])).

cnf(c_1234,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1155,c_0])).

cnf(c_1236,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1235,c_1234])).

cnf(c_73305,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_73304,c_1148,c_1236])).

cnf(c_12697,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(superposition,[status(thm)],[c_0,c_12357])).

cnf(c_74903,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_73305,c_12697])).

cnf(c_74095,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(demodulation,[status(thm)],[c_72761,c_3073])).

cnf(c_74904,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_74903,c_74095])).

cnf(c_862,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_894,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(demodulation,[status(thm)],[c_862,c_863,c_884])).

cnf(c_895,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(demodulation,[status(thm)],[c_894,c_8])).

cnf(c_5793,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_997])).

cnf(c_74905,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(demodulation,[status(thm)],[c_74904,c_895,c_5793])).

cnf(c_74906,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(demodulation,[status(thm)],[c_74905,c_1])).

cnf(c_10,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_375,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_10,c_12])).

cnf(c_691,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_0,c_375])).

cnf(c_76136,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_74906,c_691])).

cnf(c_197,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1405,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_3005,plain,
    ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | X0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_1405])).

cnf(c_9669,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_3005])).

cnf(c_7345,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1381,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))
    | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),X0)
    | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2906,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_738,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76136,c_9669,c_7345,c_2906,c_738])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.62/3.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.62/3.96  
% 27.62/3.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.62/3.96  
% 27.62/3.96  ------  iProver source info
% 27.62/3.96  
% 27.62/3.96  git: date: 2020-06-30 10:37:57 +0100
% 27.62/3.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.62/3.96  git: non_committed_changes: false
% 27.62/3.96  git: last_make_outside_of_git: false
% 27.62/3.96  
% 27.62/3.96  ------ 
% 27.62/3.96  
% 27.62/3.96  ------ Input Options
% 27.62/3.96  
% 27.62/3.96  --out_options                           all
% 27.62/3.96  --tptp_safe_out                         true
% 27.62/3.96  --problem_path                          ""
% 27.62/3.96  --include_path                          ""
% 27.62/3.96  --clausifier                            res/vclausify_rel
% 27.62/3.96  --clausifier_options                    ""
% 27.62/3.96  --stdin                                 false
% 27.62/3.96  --stats_out                             all
% 27.62/3.96  
% 27.62/3.96  ------ General Options
% 27.62/3.96  
% 27.62/3.96  --fof                                   false
% 27.62/3.96  --time_out_real                         305.
% 27.62/3.96  --time_out_virtual                      -1.
% 27.62/3.96  --symbol_type_check                     false
% 27.62/3.96  --clausify_out                          false
% 27.62/3.96  --sig_cnt_out                           false
% 27.62/3.96  --trig_cnt_out                          false
% 27.62/3.96  --trig_cnt_out_tolerance                1.
% 27.62/3.96  --trig_cnt_out_sk_spl                   false
% 27.62/3.96  --abstr_cl_out                          false
% 27.62/3.96  
% 27.62/3.96  ------ Global Options
% 27.62/3.96  
% 27.62/3.96  --schedule                              default
% 27.62/3.96  --add_important_lit                     false
% 27.62/3.96  --prop_solver_per_cl                    1000
% 27.62/3.96  --min_unsat_core                        false
% 27.62/3.96  --soft_assumptions                      false
% 27.62/3.96  --soft_lemma_size                       3
% 27.62/3.96  --prop_impl_unit_size                   0
% 27.62/3.96  --prop_impl_unit                        []
% 27.62/3.96  --share_sel_clauses                     true
% 27.62/3.96  --reset_solvers                         false
% 27.62/3.96  --bc_imp_inh                            [conj_cone]
% 27.62/3.96  --conj_cone_tolerance                   3.
% 27.62/3.96  --extra_neg_conj                        none
% 27.62/3.96  --large_theory_mode                     true
% 27.62/3.96  --prolific_symb_bound                   200
% 27.62/3.96  --lt_threshold                          2000
% 27.62/3.96  --clause_weak_htbl                      true
% 27.62/3.96  --gc_record_bc_elim                     false
% 27.62/3.96  
% 27.62/3.96  ------ Preprocessing Options
% 27.62/3.96  
% 27.62/3.96  --preprocessing_flag                    true
% 27.62/3.96  --time_out_prep_mult                    0.1
% 27.62/3.96  --splitting_mode                        input
% 27.62/3.96  --splitting_grd                         true
% 27.62/3.96  --splitting_cvd                         false
% 27.62/3.96  --splitting_cvd_svl                     false
% 27.62/3.96  --splitting_nvd                         32
% 27.62/3.96  --sub_typing                            true
% 27.62/3.96  --prep_gs_sim                           true
% 27.62/3.96  --prep_unflatten                        true
% 27.62/3.96  --prep_res_sim                          true
% 27.62/3.96  --prep_upred                            true
% 27.62/3.96  --prep_sem_filter                       exhaustive
% 27.62/3.96  --prep_sem_filter_out                   false
% 27.62/3.96  --pred_elim                             true
% 27.62/3.96  --res_sim_input                         true
% 27.62/3.96  --eq_ax_congr_red                       true
% 27.62/3.96  --pure_diseq_elim                       true
% 27.62/3.96  --brand_transform                       false
% 27.62/3.96  --non_eq_to_eq                          false
% 27.62/3.96  --prep_def_merge                        true
% 27.62/3.96  --prep_def_merge_prop_impl              false
% 27.62/3.96  --prep_def_merge_mbd                    true
% 27.62/3.96  --prep_def_merge_tr_red                 false
% 27.62/3.96  --prep_def_merge_tr_cl                  false
% 27.62/3.96  --smt_preprocessing                     true
% 27.62/3.96  --smt_ac_axioms                         fast
% 27.62/3.96  --preprocessed_out                      false
% 27.62/3.96  --preprocessed_stats                    false
% 27.62/3.96  
% 27.62/3.96  ------ Abstraction refinement Options
% 27.62/3.96  
% 27.62/3.96  --abstr_ref                             []
% 27.62/3.96  --abstr_ref_prep                        false
% 27.62/3.96  --abstr_ref_until_sat                   false
% 27.62/3.96  --abstr_ref_sig_restrict                funpre
% 27.62/3.96  --abstr_ref_af_restrict_to_split_sk     false
% 27.62/3.96  --abstr_ref_under                       []
% 27.62/3.96  
% 27.62/3.96  ------ SAT Options
% 27.62/3.96  
% 27.62/3.96  --sat_mode                              false
% 27.62/3.96  --sat_fm_restart_options                ""
% 27.62/3.96  --sat_gr_def                            false
% 27.62/3.96  --sat_epr_types                         true
% 27.62/3.96  --sat_non_cyclic_types                  false
% 27.62/3.96  --sat_finite_models                     false
% 27.62/3.96  --sat_fm_lemmas                         false
% 27.62/3.96  --sat_fm_prep                           false
% 27.62/3.96  --sat_fm_uc_incr                        true
% 27.62/3.96  --sat_out_model                         small
% 27.62/3.96  --sat_out_clauses                       false
% 27.62/3.96  
% 27.62/3.96  ------ QBF Options
% 27.62/3.96  
% 27.62/3.96  --qbf_mode                              false
% 27.62/3.96  --qbf_elim_univ                         false
% 27.62/3.96  --qbf_dom_inst                          none
% 27.62/3.96  --qbf_dom_pre_inst                      false
% 27.62/3.96  --qbf_sk_in                             false
% 27.62/3.96  --qbf_pred_elim                         true
% 27.62/3.96  --qbf_split                             512
% 27.62/3.96  
% 27.62/3.96  ------ BMC1 Options
% 27.62/3.96  
% 27.62/3.96  --bmc1_incremental                      false
% 27.62/3.96  --bmc1_axioms                           reachable_all
% 27.62/3.96  --bmc1_min_bound                        0
% 27.62/3.96  --bmc1_max_bound                        -1
% 27.62/3.96  --bmc1_max_bound_default                -1
% 27.62/3.96  --bmc1_symbol_reachability              true
% 27.62/3.96  --bmc1_property_lemmas                  false
% 27.62/3.96  --bmc1_k_induction                      false
% 27.62/3.96  --bmc1_non_equiv_states                 false
% 27.62/3.96  --bmc1_deadlock                         false
% 27.62/3.96  --bmc1_ucm                              false
% 27.62/3.96  --bmc1_add_unsat_core                   none
% 27.62/3.96  --bmc1_unsat_core_children              false
% 27.62/3.96  --bmc1_unsat_core_extrapolate_axioms    false
% 27.62/3.96  --bmc1_out_stat                         full
% 27.62/3.96  --bmc1_ground_init                      false
% 27.62/3.96  --bmc1_pre_inst_next_state              false
% 27.62/3.96  --bmc1_pre_inst_state                   false
% 27.62/3.96  --bmc1_pre_inst_reach_state             false
% 27.62/3.96  --bmc1_out_unsat_core                   false
% 27.62/3.96  --bmc1_aig_witness_out                  false
% 27.62/3.96  --bmc1_verbose                          false
% 27.62/3.96  --bmc1_dump_clauses_tptp                false
% 27.62/3.96  --bmc1_dump_unsat_core_tptp             false
% 27.62/3.96  --bmc1_dump_file                        -
% 27.62/3.96  --bmc1_ucm_expand_uc_limit              128
% 27.62/3.96  --bmc1_ucm_n_expand_iterations          6
% 27.62/3.96  --bmc1_ucm_extend_mode                  1
% 27.62/3.96  --bmc1_ucm_init_mode                    2
% 27.62/3.96  --bmc1_ucm_cone_mode                    none
% 27.62/3.96  --bmc1_ucm_reduced_relation_type        0
% 27.62/3.96  --bmc1_ucm_relax_model                  4
% 27.62/3.96  --bmc1_ucm_full_tr_after_sat            true
% 27.62/3.96  --bmc1_ucm_expand_neg_assumptions       false
% 27.62/3.96  --bmc1_ucm_layered_model                none
% 27.62/3.96  --bmc1_ucm_max_lemma_size               10
% 27.62/3.96  
% 27.62/3.96  ------ AIG Options
% 27.62/3.96  
% 27.62/3.96  --aig_mode                              false
% 27.62/3.96  
% 27.62/3.96  ------ Instantiation Options
% 27.62/3.96  
% 27.62/3.96  --instantiation_flag                    true
% 27.62/3.96  --inst_sos_flag                         true
% 27.62/3.96  --inst_sos_phase                        true
% 27.62/3.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.62/3.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.62/3.96  --inst_lit_sel_side                     num_symb
% 27.62/3.96  --inst_solver_per_active                1400
% 27.62/3.96  --inst_solver_calls_frac                1.
% 27.62/3.96  --inst_passive_queue_type               priority_queues
% 27.62/3.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.62/3.96  --inst_passive_queues_freq              [25;2]
% 27.62/3.96  --inst_dismatching                      true
% 27.62/3.96  --inst_eager_unprocessed_to_passive     true
% 27.62/3.96  --inst_prop_sim_given                   true
% 27.62/3.96  --inst_prop_sim_new                     false
% 27.62/3.96  --inst_subs_new                         false
% 27.62/3.96  --inst_eq_res_simp                      false
% 27.62/3.96  --inst_subs_given                       false
% 27.62/3.96  --inst_orphan_elimination               true
% 27.62/3.96  --inst_learning_loop_flag               true
% 27.62/3.96  --inst_learning_start                   3000
% 27.62/3.96  --inst_learning_factor                  2
% 27.62/3.96  --inst_start_prop_sim_after_learn       3
% 27.62/3.96  --inst_sel_renew                        solver
% 27.62/3.96  --inst_lit_activity_flag                true
% 27.62/3.96  --inst_restr_to_given                   false
% 27.62/3.96  --inst_activity_threshold               500
% 27.62/3.96  --inst_out_proof                        true
% 27.62/3.96  
% 27.62/3.96  ------ Resolution Options
% 27.62/3.96  
% 27.62/3.96  --resolution_flag                       true
% 27.62/3.96  --res_lit_sel                           adaptive
% 27.62/3.96  --res_lit_sel_side                      none
% 27.62/3.96  --res_ordering                          kbo
% 27.62/3.96  --res_to_prop_solver                    active
% 27.62/3.96  --res_prop_simpl_new                    false
% 27.62/3.96  --res_prop_simpl_given                  true
% 27.62/3.96  --res_passive_queue_type                priority_queues
% 27.62/3.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.62/3.96  --res_passive_queues_freq               [15;5]
% 27.62/3.96  --res_forward_subs                      full
% 27.62/3.96  --res_backward_subs                     full
% 27.62/3.96  --res_forward_subs_resolution           true
% 27.62/3.96  --res_backward_subs_resolution          true
% 27.62/3.96  --res_orphan_elimination                true
% 27.62/3.96  --res_time_limit                        2.
% 27.62/3.96  --res_out_proof                         true
% 27.62/3.96  
% 27.62/3.96  ------ Superposition Options
% 27.62/3.96  
% 27.62/3.96  --superposition_flag                    true
% 27.62/3.96  --sup_passive_queue_type                priority_queues
% 27.62/3.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.62/3.96  --sup_passive_queues_freq               [8;1;4]
% 27.62/3.96  --demod_completeness_check              fast
% 27.62/3.96  --demod_use_ground                      true
% 27.62/3.96  --sup_to_prop_solver                    passive
% 27.62/3.96  --sup_prop_simpl_new                    true
% 27.62/3.96  --sup_prop_simpl_given                  true
% 27.62/3.96  --sup_fun_splitting                     true
% 27.62/3.96  --sup_smt_interval                      50000
% 27.62/3.96  
% 27.62/3.96  ------ Superposition Simplification Setup
% 27.62/3.96  
% 27.62/3.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.62/3.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.62/3.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.62/3.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.62/3.96  --sup_full_triv                         [TrivRules;PropSubs]
% 27.62/3.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.62/3.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.62/3.96  --sup_immed_triv                        [TrivRules]
% 27.62/3.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.62/3.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.62/3.96  --sup_immed_bw_main                     []
% 27.62/3.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.62/3.96  --sup_input_triv                        [Unflattening;TrivRules]
% 27.62/3.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.62/3.96  --sup_input_bw                          []
% 27.62/3.96  
% 27.62/3.96  ------ Combination Options
% 27.62/3.96  
% 27.62/3.96  --comb_res_mult                         3
% 27.62/3.96  --comb_sup_mult                         2
% 27.62/3.96  --comb_inst_mult                        10
% 27.62/3.96  
% 27.62/3.96  ------ Debug Options
% 27.62/3.96  
% 27.62/3.96  --dbg_backtrace                         false
% 27.62/3.96  --dbg_dump_prop_clauses                 false
% 27.62/3.96  --dbg_dump_prop_clauses_file            -
% 27.62/3.96  --dbg_out_stat                          false
% 27.62/3.96  ------ Parsing...
% 27.62/3.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.62/3.96  
% 27.62/3.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.62/3.96  
% 27.62/3.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.62/3.96  
% 27.62/3.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.62/3.96  ------ Proving...
% 27.62/3.96  ------ Problem Properties 
% 27.62/3.96  
% 27.62/3.96  
% 27.62/3.96  clauses                                 12
% 27.62/3.96  conjectures                             3
% 27.62/3.96  EPR                                     3
% 27.62/3.96  Horn                                    12
% 27.62/3.96  unary                                   9
% 27.62/3.96  binary                                  2
% 27.62/3.96  lits                                    16
% 27.62/3.96  lits eq                                 9
% 27.62/3.96  fd_pure                                 0
% 27.62/3.96  fd_pseudo                               0
% 27.62/3.96  fd_cond                                 0
% 27.62/3.96  fd_pseudo_cond                          1
% 27.62/3.96  AC symbols                              0
% 27.62/3.96  
% 27.62/3.96  ------ Schedule dynamic 5 is on 
% 27.62/3.96  
% 27.62/3.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.62/3.96  
% 27.62/3.96  
% 27.62/3.96  ------ 
% 27.62/3.96  Current options:
% 27.62/3.96  ------ 
% 27.62/3.96  
% 27.62/3.96  ------ Input Options
% 27.62/3.96  
% 27.62/3.96  --out_options                           all
% 27.62/3.96  --tptp_safe_out                         true
% 27.62/3.96  --problem_path                          ""
% 27.62/3.96  --include_path                          ""
% 27.62/3.96  --clausifier                            res/vclausify_rel
% 27.62/3.96  --clausifier_options                    ""
% 27.62/3.96  --stdin                                 false
% 27.62/3.96  --stats_out                             all
% 27.62/3.96  
% 27.62/3.96  ------ General Options
% 27.62/3.96  
% 27.62/3.96  --fof                                   false
% 27.62/3.96  --time_out_real                         305.
% 27.62/3.96  --time_out_virtual                      -1.
% 27.62/3.96  --symbol_type_check                     false
% 27.62/3.96  --clausify_out                          false
% 27.62/3.96  --sig_cnt_out                           false
% 27.62/3.96  --trig_cnt_out                          false
% 27.62/3.96  --trig_cnt_out_tolerance                1.
% 27.62/3.96  --trig_cnt_out_sk_spl                   false
% 27.62/3.96  --abstr_cl_out                          false
% 27.62/3.96  
% 27.62/3.96  ------ Global Options
% 27.62/3.96  
% 27.62/3.96  --schedule                              default
% 27.62/3.96  --add_important_lit                     false
% 27.62/3.96  --prop_solver_per_cl                    1000
% 27.62/3.96  --min_unsat_core                        false
% 27.62/3.96  --soft_assumptions                      false
% 27.62/3.96  --soft_lemma_size                       3
% 27.62/3.96  --prop_impl_unit_size                   0
% 27.62/3.96  --prop_impl_unit                        []
% 27.62/3.96  --share_sel_clauses                     true
% 27.62/3.96  --reset_solvers                         false
% 27.62/3.96  --bc_imp_inh                            [conj_cone]
% 27.62/3.96  --conj_cone_tolerance                   3.
% 27.62/3.96  --extra_neg_conj                        none
% 27.62/3.96  --large_theory_mode                     true
% 27.62/3.96  --prolific_symb_bound                   200
% 27.62/3.96  --lt_threshold                          2000
% 27.62/3.96  --clause_weak_htbl                      true
% 27.62/3.96  --gc_record_bc_elim                     false
% 27.62/3.96  
% 27.62/3.96  ------ Preprocessing Options
% 27.62/3.96  
% 27.62/3.96  --preprocessing_flag                    true
% 27.62/3.96  --time_out_prep_mult                    0.1
% 27.62/3.96  --splitting_mode                        input
% 27.62/3.96  --splitting_grd                         true
% 27.62/3.96  --splitting_cvd                         false
% 27.62/3.96  --splitting_cvd_svl                     false
% 27.62/3.96  --splitting_nvd                         32
% 27.62/3.96  --sub_typing                            true
% 27.62/3.96  --prep_gs_sim                           true
% 27.62/3.96  --prep_unflatten                        true
% 27.62/3.96  --prep_res_sim                          true
% 27.62/3.96  --prep_upred                            true
% 27.62/3.96  --prep_sem_filter                       exhaustive
% 27.62/3.96  --prep_sem_filter_out                   false
% 27.62/3.96  --pred_elim                             true
% 27.62/3.96  --res_sim_input                         true
% 27.62/3.96  --eq_ax_congr_red                       true
% 27.62/3.96  --pure_diseq_elim                       true
% 27.62/3.96  --brand_transform                       false
% 27.62/3.96  --non_eq_to_eq                          false
% 27.62/3.96  --prep_def_merge                        true
% 27.62/3.96  --prep_def_merge_prop_impl              false
% 27.62/3.96  --prep_def_merge_mbd                    true
% 27.62/3.96  --prep_def_merge_tr_red                 false
% 27.62/3.96  --prep_def_merge_tr_cl                  false
% 27.62/3.96  --smt_preprocessing                     true
% 27.62/3.96  --smt_ac_axioms                         fast
% 27.62/3.96  --preprocessed_out                      false
% 27.62/3.96  --preprocessed_stats                    false
% 27.62/3.96  
% 27.62/3.96  ------ Abstraction refinement Options
% 27.62/3.96  
% 27.62/3.96  --abstr_ref                             []
% 27.62/3.96  --abstr_ref_prep                        false
% 27.62/3.96  --abstr_ref_until_sat                   false
% 27.62/3.96  --abstr_ref_sig_restrict                funpre
% 27.62/3.96  --abstr_ref_af_restrict_to_split_sk     false
% 27.62/3.96  --abstr_ref_under                       []
% 27.62/3.96  
% 27.62/3.96  ------ SAT Options
% 27.62/3.96  
% 27.62/3.96  --sat_mode                              false
% 27.62/3.96  --sat_fm_restart_options                ""
% 27.62/3.96  --sat_gr_def                            false
% 27.62/3.96  --sat_epr_types                         true
% 27.62/3.96  --sat_non_cyclic_types                  false
% 27.62/3.96  --sat_finite_models                     false
% 27.62/3.96  --sat_fm_lemmas                         false
% 27.62/3.96  --sat_fm_prep                           false
% 27.62/3.96  --sat_fm_uc_incr                        true
% 27.62/3.96  --sat_out_model                         small
% 27.62/3.96  --sat_out_clauses                       false
% 27.62/3.96  
% 27.62/3.96  ------ QBF Options
% 27.62/3.96  
% 27.62/3.96  --qbf_mode                              false
% 27.62/3.96  --qbf_elim_univ                         false
% 27.62/3.96  --qbf_dom_inst                          none
% 27.62/3.96  --qbf_dom_pre_inst                      false
% 27.62/3.96  --qbf_sk_in                             false
% 27.62/3.96  --qbf_pred_elim                         true
% 27.62/3.96  --qbf_split                             512
% 27.62/3.96  
% 27.62/3.96  ------ BMC1 Options
% 27.62/3.96  
% 27.62/3.96  --bmc1_incremental                      false
% 27.62/3.96  --bmc1_axioms                           reachable_all
% 27.62/3.96  --bmc1_min_bound                        0
% 27.62/3.96  --bmc1_max_bound                        -1
% 27.62/3.96  --bmc1_max_bound_default                -1
% 27.62/3.96  --bmc1_symbol_reachability              true
% 27.62/3.96  --bmc1_property_lemmas                  false
% 27.62/3.96  --bmc1_k_induction                      false
% 27.62/3.96  --bmc1_non_equiv_states                 false
% 27.62/3.96  --bmc1_deadlock                         false
% 27.62/3.96  --bmc1_ucm                              false
% 27.62/3.96  --bmc1_add_unsat_core                   none
% 27.62/3.96  --bmc1_unsat_core_children              false
% 27.62/3.96  --bmc1_unsat_core_extrapolate_axioms    false
% 27.62/3.96  --bmc1_out_stat                         full
% 27.62/3.96  --bmc1_ground_init                      false
% 27.62/3.96  --bmc1_pre_inst_next_state              false
% 27.62/3.96  --bmc1_pre_inst_state                   false
% 27.62/3.96  --bmc1_pre_inst_reach_state             false
% 27.62/3.96  --bmc1_out_unsat_core                   false
% 27.62/3.96  --bmc1_aig_witness_out                  false
% 27.62/3.96  --bmc1_verbose                          false
% 27.62/3.96  --bmc1_dump_clauses_tptp                false
% 27.62/3.96  --bmc1_dump_unsat_core_tptp             false
% 27.62/3.96  --bmc1_dump_file                        -
% 27.62/3.96  --bmc1_ucm_expand_uc_limit              128
% 27.62/3.96  --bmc1_ucm_n_expand_iterations          6
% 27.62/3.96  --bmc1_ucm_extend_mode                  1
% 27.62/3.96  --bmc1_ucm_init_mode                    2
% 27.62/3.96  --bmc1_ucm_cone_mode                    none
% 27.62/3.96  --bmc1_ucm_reduced_relation_type        0
% 27.62/3.96  --bmc1_ucm_relax_model                  4
% 27.62/3.96  --bmc1_ucm_full_tr_after_sat            true
% 27.62/3.96  --bmc1_ucm_expand_neg_assumptions       false
% 27.62/3.96  --bmc1_ucm_layered_model                none
% 27.62/3.96  --bmc1_ucm_max_lemma_size               10
% 27.62/3.96  
% 27.62/3.96  ------ AIG Options
% 27.62/3.96  
% 27.62/3.96  --aig_mode                              false
% 27.62/3.96  
% 27.62/3.96  ------ Instantiation Options
% 27.62/3.96  
% 27.62/3.96  --instantiation_flag                    true
% 27.62/3.96  --inst_sos_flag                         true
% 27.62/3.96  --inst_sos_phase                        true
% 27.62/3.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.62/3.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.62/3.96  --inst_lit_sel_side                     none
% 27.62/3.96  --inst_solver_per_active                1400
% 27.62/3.96  --inst_solver_calls_frac                1.
% 27.62/3.96  --inst_passive_queue_type               priority_queues
% 27.62/3.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.62/3.96  --inst_passive_queues_freq              [25;2]
% 27.62/3.96  --inst_dismatching                      true
% 27.62/3.96  --inst_eager_unprocessed_to_passive     true
% 27.62/3.96  --inst_prop_sim_given                   true
% 27.62/3.96  --inst_prop_sim_new                     false
% 27.62/3.96  --inst_subs_new                         false
% 27.62/3.96  --inst_eq_res_simp                      false
% 27.62/3.96  --inst_subs_given                       false
% 27.62/3.96  --inst_orphan_elimination               true
% 27.62/3.96  --inst_learning_loop_flag               true
% 27.62/3.96  --inst_learning_start                   3000
% 27.62/3.96  --inst_learning_factor                  2
% 27.62/3.96  --inst_start_prop_sim_after_learn       3
% 27.62/3.96  --inst_sel_renew                        solver
% 27.62/3.96  --inst_lit_activity_flag                true
% 27.62/3.96  --inst_restr_to_given                   false
% 27.62/3.96  --inst_activity_threshold               500
% 27.62/3.96  --inst_out_proof                        true
% 27.62/3.96  
% 27.62/3.96  ------ Resolution Options
% 27.62/3.96  
% 27.62/3.96  --resolution_flag                       false
% 27.62/3.96  --res_lit_sel                           adaptive
% 27.62/3.96  --res_lit_sel_side                      none
% 27.62/3.96  --res_ordering                          kbo
% 27.62/3.96  --res_to_prop_solver                    active
% 27.62/3.96  --res_prop_simpl_new                    false
% 27.62/3.96  --res_prop_simpl_given                  true
% 27.62/3.96  --res_passive_queue_type                priority_queues
% 27.62/3.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.62/3.96  --res_passive_queues_freq               [15;5]
% 27.62/3.96  --res_forward_subs                      full
% 27.62/3.96  --res_backward_subs                     full
% 27.62/3.96  --res_forward_subs_resolution           true
% 27.62/3.96  --res_backward_subs_resolution          true
% 27.62/3.96  --res_orphan_elimination                true
% 27.62/3.96  --res_time_limit                        2.
% 27.62/3.96  --res_out_proof                         true
% 27.62/3.96  
% 27.62/3.96  ------ Superposition Options
% 27.62/3.96  
% 27.62/3.96  --superposition_flag                    true
% 27.62/3.96  --sup_passive_queue_type                priority_queues
% 27.62/3.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.62/3.96  --sup_passive_queues_freq               [8;1;4]
% 27.62/3.96  --demod_completeness_check              fast
% 27.62/3.96  --demod_use_ground                      true
% 27.62/3.96  --sup_to_prop_solver                    passive
% 27.62/3.96  --sup_prop_simpl_new                    true
% 27.62/3.96  --sup_prop_simpl_given                  true
% 27.62/3.96  --sup_fun_splitting                     true
% 27.62/3.96  --sup_smt_interval                      50000
% 27.62/3.96  
% 27.62/3.96  ------ Superposition Simplification Setup
% 27.62/3.96  
% 27.62/3.96  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.62/3.96  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.62/3.96  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.62/3.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.62/3.96  --sup_full_triv                         [TrivRules;PropSubs]
% 27.62/3.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.62/3.96  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.62/3.96  --sup_immed_triv                        [TrivRules]
% 27.62/3.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.62/3.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.62/3.96  --sup_immed_bw_main                     []
% 27.62/3.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.62/3.96  --sup_input_triv                        [Unflattening;TrivRules]
% 27.62/3.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.62/3.96  --sup_input_bw                          []
% 27.62/3.96  
% 27.62/3.96  ------ Combination Options
% 27.62/3.96  
% 27.62/3.96  --comb_res_mult                         3
% 27.62/3.96  --comb_sup_mult                         2
% 27.62/3.96  --comb_inst_mult                        10
% 27.62/3.96  
% 27.62/3.96  ------ Debug Options
% 27.62/3.96  
% 27.62/3.96  --dbg_backtrace                         false
% 27.62/3.96  --dbg_dump_prop_clauses                 false
% 27.62/3.96  --dbg_dump_prop_clauses_file            -
% 27.62/3.96  --dbg_out_stat                          false
% 27.62/3.96  
% 27.62/3.96  
% 27.62/3.96  
% 27.62/3.96  
% 27.62/3.96  ------ Proving...
% 27.62/3.96  
% 27.62/3.96  
% 27.62/3.96  % SZS status Theorem for theBenchmark.p
% 27.62/3.96  
% 27.62/3.96  % SZS output start CNFRefutation for theBenchmark.p
% 27.62/3.96  
% 27.62/3.96  fof(f1,axiom,(
% 27.62/3.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f24,plain,(
% 27.62/3.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.62/3.96    inference(cnf_transformation,[],[f1])).
% 27.62/3.96  
% 27.62/3.96  fof(f7,axiom,(
% 27.62/3.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f33,plain,(
% 27.62/3.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.62/3.96    inference(cnf_transformation,[],[f7])).
% 27.62/3.96  
% 27.62/3.96  fof(f44,plain,(
% 27.62/3.96    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 27.62/3.96    inference(definition_unfolding,[],[f24,f33,f33])).
% 27.62/3.96  
% 27.62/3.96  fof(f11,axiom,(
% 27.62/3.96    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f15,plain,(
% 27.62/3.96    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 27.62/3.96    inference(unused_predicate_definition_removal,[],[f11])).
% 27.62/3.96  
% 27.62/3.96  fof(f16,plain,(
% 27.62/3.96    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 27.62/3.96    inference(ennf_transformation,[],[f15])).
% 27.62/3.96  
% 27.62/3.96  fof(f37,plain,(
% 27.62/3.96    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 27.62/3.96    inference(cnf_transformation,[],[f16])).
% 27.62/3.96  
% 27.62/3.96  fof(f8,axiom,(
% 27.62/3.96    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f34,plain,(
% 27.62/3.96    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.62/3.96    inference(cnf_transformation,[],[f8])).
% 27.62/3.96  
% 27.62/3.96  fof(f9,axiom,(
% 27.62/3.96    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f35,plain,(
% 27.62/3.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.62/3.96    inference(cnf_transformation,[],[f9])).
% 27.62/3.96  
% 27.62/3.96  fof(f10,axiom,(
% 27.62/3.96    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f36,plain,(
% 27.62/3.96    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.62/3.96    inference(cnf_transformation,[],[f10])).
% 27.62/3.96  
% 27.62/3.96  fof(f42,plain,(
% 27.62/3.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 27.62/3.96    inference(definition_unfolding,[],[f35,f36])).
% 27.62/3.96  
% 27.62/3.96  fof(f43,plain,(
% 27.62/3.96    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 27.62/3.96    inference(definition_unfolding,[],[f34,f42])).
% 27.62/3.96  
% 27.62/3.96  fof(f48,plain,(
% 27.62/3.96    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 27.62/3.96    inference(definition_unfolding,[],[f37,f43])).
% 27.62/3.96  
% 27.62/3.96  fof(f12,conjecture,(
% 27.62/3.96    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f13,negated_conjecture,(
% 27.62/3.96    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 27.62/3.96    inference(negated_conjecture,[],[f12])).
% 27.62/3.96  
% 27.62/3.96  fof(f17,plain,(
% 27.62/3.96    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 27.62/3.96    inference(ennf_transformation,[],[f13])).
% 27.62/3.96  
% 27.62/3.96  fof(f18,plain,(
% 27.62/3.96    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 27.62/3.96    inference(flattening,[],[f17])).
% 27.62/3.96  
% 27.62/3.96  fof(f22,plain,(
% 27.62/3.96    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1))),
% 27.62/3.96    introduced(choice_axiom,[])).
% 27.62/3.96  
% 27.62/3.96  fof(f23,plain,(
% 27.62/3.96    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1)),
% 27.62/3.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).
% 27.62/3.96  
% 27.62/3.96  fof(f40,plain,(
% 27.62/3.96    r2_hidden(sK3,sK0)),
% 27.62/3.96    inference(cnf_transformation,[],[f23])).
% 27.62/3.96  
% 27.62/3.96  fof(f39,plain,(
% 27.62/3.96    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 27.62/3.96    inference(cnf_transformation,[],[f23])).
% 27.62/3.96  
% 27.62/3.96  fof(f50,plain,(
% 27.62/3.96    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 27.62/3.96    inference(definition_unfolding,[],[f39,f33,f43])).
% 27.62/3.96  
% 27.62/3.96  fof(f4,axiom,(
% 27.62/3.96    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f21,plain,(
% 27.62/3.96    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 27.62/3.96    inference(nnf_transformation,[],[f4])).
% 27.62/3.96  
% 27.62/3.96  fof(f30,plain,(
% 27.62/3.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.62/3.96    inference(cnf_transformation,[],[f21])).
% 27.62/3.96  
% 27.62/3.96  fof(f5,axiom,(
% 27.62/3.96    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f31,plain,(
% 27.62/3.96    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 27.62/3.96    inference(cnf_transformation,[],[f5])).
% 27.62/3.96  
% 27.62/3.96  fof(f46,plain,(
% 27.62/3.96    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 27.62/3.96    inference(definition_unfolding,[],[f31,f33,f33,f33,f33])).
% 27.62/3.96  
% 27.62/3.96  fof(f38,plain,(
% 27.62/3.96    r1_tarski(sK0,sK1)),
% 27.62/3.96    inference(cnf_transformation,[],[f23])).
% 27.62/3.96  
% 27.62/3.96  fof(f6,axiom,(
% 27.62/3.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f32,plain,(
% 27.62/3.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.62/3.96    inference(cnf_transformation,[],[f6])).
% 27.62/3.96  
% 27.62/3.96  fof(f47,plain,(
% 27.62/3.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.62/3.96    inference(definition_unfolding,[],[f32,f33])).
% 27.62/3.96  
% 27.62/3.96  fof(f2,axiom,(
% 27.62/3.96    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f14,plain,(
% 27.62/3.96    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 27.62/3.96    inference(rectify,[],[f2])).
% 27.62/3.96  
% 27.62/3.96  fof(f25,plain,(
% 27.62/3.96    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 27.62/3.96    inference(cnf_transformation,[],[f14])).
% 27.62/3.96  
% 27.62/3.96  fof(f45,plain,(
% 27.62/3.96    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 27.62/3.96    inference(definition_unfolding,[],[f25,f33])).
% 27.62/3.96  
% 27.62/3.96  fof(f3,axiom,(
% 27.62/3.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.62/3.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.62/3.96  
% 27.62/3.96  fof(f19,plain,(
% 27.62/3.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.62/3.96    inference(nnf_transformation,[],[f3])).
% 27.62/3.96  
% 27.62/3.96  fof(f20,plain,(
% 27.62/3.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.62/3.96    inference(flattening,[],[f19])).
% 27.62/3.96  
% 27.62/3.96  fof(f26,plain,(
% 27.62/3.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.62/3.96    inference(cnf_transformation,[],[f20])).
% 27.62/3.96  
% 27.62/3.96  fof(f52,plain,(
% 27.62/3.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.62/3.96    inference(equality_resolution,[],[f26])).
% 27.62/3.96  
% 27.62/3.96  fof(f41,plain,(
% 27.62/3.96    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 27.62/3.96    inference(cnf_transformation,[],[f23])).
% 27.62/3.96  
% 27.62/3.96  fof(f49,plain,(
% 27.62/3.96    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 27.62/3.96    inference(definition_unfolding,[],[f41,f33,f43])).
% 27.62/3.96  
% 27.62/3.96  fof(f28,plain,(
% 27.62/3.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.62/3.96    inference(cnf_transformation,[],[f20])).
% 27.62/3.96  
% 27.62/3.96  cnf(c_0,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.62/3.96      inference(cnf_transformation,[],[f44]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_9,plain,
% 27.62/3.96      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 27.62/3.96      inference(cnf_transformation,[],[f48]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_11,negated_conjecture,
% 27.62/3.96      ( r2_hidden(sK3,sK0) ),
% 27.62/3.96      inference(cnf_transformation,[],[f40]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_121,plain,
% 27.62/3.96      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | sK3 != X0 | sK0 != X1 ),
% 27.62/3.96      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_122,plain,
% 27.62/3.96      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),sK0) ),
% 27.62/3.96      inference(unflattening,[status(thm)],[c_121]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_369,plain,
% 27.62/3.96      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK3),sK0) = iProver_top ),
% 27.62/3.96      inference(predicate_to_equality,[status(thm)],[c_122]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_12,negated_conjecture,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 27.62/3.96      inference(cnf_transformation,[],[f50]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_510,plain,
% 27.62/3.96      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) = iProver_top ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_369,c_12]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_690,plain,
% 27.62/3.96      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = iProver_top ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_0,c_510]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_5,plain,
% 27.62/3.96      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 27.62/3.96      inference(cnf_transformation,[],[f30]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_372,plain,
% 27.62/3.96      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 27.62/3.96      | r1_tarski(X0,X1) != iProver_top ),
% 27.62/3.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1148,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = k1_xboole_0 ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_690,c_372]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_7,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 27.62/3.96      inference(cnf_transformation,[],[f46]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1248,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1148,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_13,negated_conjecture,
% 27.62/3.96      ( r1_tarski(sK0,sK1) ),
% 27.62/3.96      inference(cnf_transformation,[],[f38]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_370,plain,
% 27.62/3.96      ( r1_tarski(sK0,sK1) = iProver_top ),
% 27.62/3.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1147,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_370,c_372]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_8,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.62/3.96      inference(cnf_transformation,[],[f47]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_767,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1154,plain,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK1,sK0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1147,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1317,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK1) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1154,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2250,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK1) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_1317]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1152,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,sK1) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1147,c_8]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1155,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_1152,c_1147]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1232,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1155,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2266,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK1) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_2250,c_1147,c_1232]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2275,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_2266,c_0]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1150,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1147,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2022,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k1_xboole_0))))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1232,c_1150]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2023,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_2022,c_1154]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2024,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_2023,c_767,c_1150]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2025,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_2024,c_1147]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2279,plain,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_2275,c_1154,c_2025]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_3073,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_1248,c_1248,c_2279]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_884,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_11939,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X2) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_884]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_12356,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_11939,c_8,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_868,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_892,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_868,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_12357,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_12356,c_8,c_892]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_12734,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_12357]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_23619,plain,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_3073,c_12734]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1343,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1150,c_0]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_3552,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_1343]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2766,plain,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X0)) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_2279,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2775,plain,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_2766,c_1150]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_4539,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_3552,c_2775]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_3635,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(sK0,k1_xboole_0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1)))))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_7,c_3552]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_863,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_3662,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK1)))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))))) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_3635,c_863]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_4605,plain,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_4539,c_767,c_3662]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_844,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_4936,plain,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1147,c_844]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_997,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_7,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_5827,plain,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k1_xboole_0)))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK0))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1147,c_997]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_24122,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0))) ),
% 27.62/3.96      inference(demodulation,
% 27.62/3.96                [status(thm)],
% 27.62/3.96                [c_23619,c_4605,c_4936,c_5827]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1012,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_767,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_72293,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k1_xboole_0)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_xboole_0)),k1_xboole_0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_24122,c_1012]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_12031,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_884,c_884]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1006,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_767,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1018,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_1006,c_863]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1019,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_1018,c_8,c_863]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_12747,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1019,c_12357]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_12741,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),X3) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_863,c_12357]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_12935,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X3) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_12741,c_863]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_13037,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X1)))),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X2) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_12031,c_12747,c_12935]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 27.62/3.96      inference(cnf_transformation,[],[f45]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_13038,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_13037,c_1,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_72635,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1012,c_13038]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_72589,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1012,c_1]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_4,plain,
% 27.62/3.96      ( r1_tarski(X0,X0) ),
% 27.62/3.96      inference(cnf_transformation,[],[f52]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_373,plain,
% 27.62/3.96      ( r1_tarski(X0,X0) = iProver_top ),
% 27.62/3.96      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1146,plain,
% 27.62/3.96      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_373,c_372]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_72761,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_72589,c_1,c_1146]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_73302,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK1) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_72293,c_72635,c_72761]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1243,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1148,c_8]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1249,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0)) = k1_xboole_0 ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_1243,c_1148]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2177,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)))) = k1_xboole_0 ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1249,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2483,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))) = k4_xboole_0(sK2,k1_xboole_0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_2177,c_8]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2574,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1))) = k4_xboole_0(sK2,k1_xboole_0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_2483]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_4960,plain,
% 27.62/3.96      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_2574,c_844]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2487,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_2483,c_2177]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_5170,plain,
% 27.62/3.96      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_4960,c_2487]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_73303,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK1) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_73302,c_5170]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_883,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_7,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_885,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_883,c_884]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_16989,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X2))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_885,c_997]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_8089,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1019,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_17010,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_16989,c_863,c_8089]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_17011,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_17010,c_1]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_25210,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_17011,c_13038]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_73304,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK1) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_73303,c_25210]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1233,plain,
% 27.62/3.96      ( k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1155,c_767]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1235,plain,
% 27.62/3.96      ( k4_xboole_0(k1_xboole_0,sK0) = k1_xboole_0 ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_1233,c_1146]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1234,plain,
% 27.62/3.96      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_1155,c_0]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1236,plain,
% 27.62/3.96      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_1235,c_1234]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_73305,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK1) = k1_xboole_0 ),
% 27.62/3.96      inference(light_normalisation,
% 27.62/3.96                [status(thm)],
% 27.62/3.96                [c_73304,c_1148,c_1236]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_12697,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_12357]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_74903,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_73305,c_12697]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_74095,plain,
% 27.62/3.96      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k1_xboole_0) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_72761,c_3073]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_74904,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_74903,c_74095]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_862,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_894,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_862,c_863,c_884]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_895,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_894,c_8]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_5793,plain,
% 27.62/3.96      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 27.62/3.96      inference(superposition,[status(thm)],[c_0,c_997]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_74905,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_74904,c_895,c_5793]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_74906,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_74905,c_1]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_10,negated_conjecture,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 27.62/3.96      inference(cnf_transformation,[],[f49]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_375,plain,
% 27.62/3.96      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 27.62/3.96      inference(light_normalisation,[status(thm)],[c_10,c_12]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_691,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_0,c_375]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_76136,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 27.62/3.96      inference(demodulation,[status(thm)],[c_74906,c_691]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_197,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1405,plain,
% 27.62/3.96      ( X0 != X1
% 27.62/3.96      | X0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
% 27.62/3.96      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != X1 ),
% 27.62/3.96      inference(instantiation,[status(thm)],[c_197]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_3005,plain,
% 27.62/3.96      ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
% 27.62/3.96      | X0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
% 27.62/3.96      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 27.62/3.96      inference(instantiation,[status(thm)],[c_1405]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_9669,plain,
% 27.62/3.96      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
% 27.62/3.96      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
% 27.62/3.96      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 27.62/3.96      inference(instantiation,[status(thm)],[c_3005]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_7345,plain,
% 27.62/3.96      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
% 27.62/3.96      inference(instantiation,[status(thm)],[c_4]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2,plain,
% 27.62/3.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.62/3.96      inference(cnf_transformation,[],[f28]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_1381,plain,
% 27.62/3.96      ( ~ r1_tarski(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))
% 27.62/3.96      | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),X0)
% 27.62/3.96      | X0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 27.62/3.96      inference(instantiation,[status(thm)],[c_2]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_2906,plain,
% 27.62/3.96      ( ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))
% 27.62/3.96      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 27.62/3.96      inference(instantiation,[status(thm)],[c_1381]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(c_738,plain,
% 27.62/3.96      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 27.62/3.96      inference(instantiation,[status(thm)],[c_0]) ).
% 27.62/3.96  
% 27.62/3.96  cnf(contradiction,plain,
% 27.62/3.96      ( $false ),
% 27.62/3.96      inference(minisat,
% 27.62/3.96                [status(thm)],
% 27.62/3.96                [c_76136,c_9669,c_7345,c_2906,c_738]) ).
% 27.62/3.96  
% 27.62/3.96  
% 27.62/3.96  % SZS output end CNFRefutation for theBenchmark.p
% 27.62/3.96  
% 27.62/3.96  ------                               Statistics
% 27.62/3.96  
% 27.62/3.96  ------ General
% 27.62/3.96  
% 27.62/3.96  abstr_ref_over_cycles:                  0
% 27.62/3.96  abstr_ref_under_cycles:                 0
% 27.62/3.96  gc_basic_clause_elim:                   0
% 27.62/3.96  forced_gc_time:                         0
% 27.62/3.96  parsing_time:                           0.008
% 27.62/3.96  unif_index_cands_time:                  0.
% 27.62/3.96  unif_index_add_time:                    0.
% 27.62/3.96  orderings_time:                         0.
% 27.62/3.96  out_proof_time:                         0.011
% 27.62/3.96  total_time:                             3.419
% 27.62/3.96  num_of_symbols:                         40
% 27.62/3.96  num_of_terms:                           144045
% 27.62/3.96  
% 27.62/3.96  ------ Preprocessing
% 27.62/3.96  
% 27.62/3.96  num_of_splits:                          0
% 27.62/3.96  num_of_split_atoms:                     0
% 27.62/3.96  num_of_reused_defs:                     0
% 27.62/3.96  num_eq_ax_congr_red:                    0
% 27.62/3.96  num_of_sem_filtered_clauses:            1
% 27.62/3.96  num_of_subtypes:                        0
% 27.62/3.96  monotx_restored_types:                  0
% 27.62/3.96  sat_num_of_epr_types:                   0
% 27.62/3.96  sat_num_of_non_cyclic_types:            0
% 27.62/3.96  sat_guarded_non_collapsed_types:        0
% 27.62/3.96  num_pure_diseq_elim:                    0
% 27.62/3.96  simp_replaced_by:                       0
% 27.62/3.96  res_preprocessed:                       60
% 27.62/3.96  prep_upred:                             0
% 27.62/3.96  prep_unflattend:                        2
% 27.62/3.96  smt_new_axioms:                         0
% 27.62/3.96  pred_elim_cands:                        1
% 27.62/3.96  pred_elim:                              1
% 27.62/3.96  pred_elim_cl:                           1
% 27.62/3.96  pred_elim_cycles:                       3
% 27.62/3.96  merged_defs:                            8
% 27.62/3.96  merged_defs_ncl:                        0
% 27.62/3.96  bin_hyper_res:                          8
% 27.62/3.96  prep_cycles:                            4
% 27.62/3.96  pred_elim_time:                         0.
% 27.62/3.96  splitting_time:                         0.
% 27.62/3.96  sem_filter_time:                        0.
% 27.62/3.96  monotx_time:                            0.001
% 27.62/3.96  subtype_inf_time:                       0.
% 27.62/3.96  
% 27.62/3.96  ------ Problem properties
% 27.62/3.96  
% 27.62/3.96  clauses:                                12
% 27.62/3.96  conjectures:                            3
% 27.62/3.96  epr:                                    3
% 27.62/3.96  horn:                                   12
% 27.62/3.96  ground:                                 4
% 27.62/3.96  unary:                                  9
% 27.62/3.96  binary:                                 2
% 27.62/3.96  lits:                                   16
% 27.62/3.96  lits_eq:                                9
% 27.62/3.96  fd_pure:                                0
% 27.62/3.96  fd_pseudo:                              0
% 27.62/3.96  fd_cond:                                0
% 27.62/3.96  fd_pseudo_cond:                         1
% 27.62/3.96  ac_symbols:                             0
% 27.62/3.96  
% 27.62/3.96  ------ Propositional Solver
% 27.62/3.96  
% 27.62/3.96  prop_solver_calls:                      33
% 27.62/3.96  prop_fast_solver_calls:                 459
% 27.62/3.96  smt_solver_calls:                       0
% 27.62/3.96  smt_fast_solver_calls:                  0
% 27.62/3.96  prop_num_of_clauses:                    16593
% 27.62/3.96  prop_preprocess_simplified:             15405
% 27.62/3.96  prop_fo_subsumed:                       0
% 27.62/3.96  prop_solver_time:                       0.
% 27.62/3.96  smt_solver_time:                        0.
% 27.62/3.96  smt_fast_solver_time:                   0.
% 27.62/3.96  prop_fast_solver_time:                  0.
% 27.62/3.96  prop_unsat_core_time:                   0.001
% 27.62/3.96  
% 27.62/3.96  ------ QBF
% 27.62/3.96  
% 27.62/3.96  qbf_q_res:                              0
% 27.62/3.96  qbf_num_tautologies:                    0
% 27.62/3.96  qbf_prep_cycles:                        0
% 27.62/3.96  
% 27.62/3.96  ------ BMC1
% 27.62/3.96  
% 27.62/3.96  bmc1_current_bound:                     -1
% 27.62/3.96  bmc1_last_solved_bound:                 -1
% 27.62/3.96  bmc1_unsat_core_size:                   -1
% 27.62/3.96  bmc1_unsat_core_parents_size:           -1
% 27.62/3.96  bmc1_merge_next_fun:                    0
% 27.62/3.96  bmc1_unsat_core_clauses_time:           0.
% 27.62/3.96  
% 27.62/3.96  ------ Instantiation
% 27.62/3.96  
% 27.62/3.96  inst_num_of_clauses:                    2396
% 27.62/3.96  inst_num_in_passive:                    908
% 27.62/3.96  inst_num_in_active:                     922
% 27.62/3.96  inst_num_in_unprocessed:                566
% 27.62/3.96  inst_num_of_loops:                      960
% 27.62/3.96  inst_num_of_learning_restarts:          0
% 27.62/3.96  inst_num_moves_active_passive:          34
% 27.62/3.96  inst_lit_activity:                      0
% 27.62/3.96  inst_lit_activity_moves:                0
% 27.62/3.96  inst_num_tautologies:                   0
% 27.62/3.96  inst_num_prop_implied:                  0
% 27.62/3.96  inst_num_existing_simplified:           0
% 27.62/3.96  inst_num_eq_res_simplified:             0
% 27.62/3.96  inst_num_child_elim:                    0
% 27.62/3.96  inst_num_of_dismatching_blockings:      735
% 27.62/3.96  inst_num_of_non_proper_insts:           3821
% 27.62/3.96  inst_num_of_duplicates:                 0
% 27.62/3.96  inst_inst_num_from_inst_to_res:         0
% 27.62/3.96  inst_dismatching_checking_time:         0.
% 27.62/3.96  
% 27.62/3.96  ------ Resolution
% 27.62/3.96  
% 27.62/3.96  res_num_of_clauses:                     0
% 27.62/3.96  res_num_in_passive:                     0
% 27.62/3.96  res_num_in_active:                      0
% 27.62/3.96  res_num_of_loops:                       64
% 27.62/3.96  res_forward_subset_subsumed:            798
% 27.62/3.96  res_backward_subset_subsumed:           0
% 27.62/3.96  res_forward_subsumed:                   0
% 27.62/3.96  res_backward_subsumed:                  0
% 27.62/3.96  res_forward_subsumption_resolution:     0
% 27.62/3.96  res_backward_subsumption_resolution:    0
% 27.62/3.96  res_clause_to_clause_subsumption:       203034
% 27.62/3.96  res_orphan_elimination:                 0
% 27.62/3.96  res_tautology_del:                      310
% 27.62/3.96  res_num_eq_res_simplified:              0
% 27.62/3.96  res_num_sel_changes:                    0
% 27.62/3.96  res_moves_from_active_to_pass:          0
% 27.62/3.96  
% 27.62/3.96  ------ Superposition
% 27.62/3.96  
% 27.62/3.96  sup_time_total:                         0.
% 27.62/3.96  sup_time_generating:                    0.
% 27.62/3.96  sup_time_sim_full:                      0.
% 27.62/3.96  sup_time_sim_immed:                     0.
% 27.62/3.96  
% 27.62/3.96  sup_num_of_clauses:                     5325
% 27.62/3.96  sup_num_in_active:                      60
% 27.62/3.96  sup_num_in_passive:                     5265
% 27.62/3.96  sup_num_of_loops:                       190
% 27.62/3.96  sup_fw_superposition:                   13661
% 27.62/3.96  sup_bw_superposition:                   13891
% 27.62/3.96  sup_immediate_simplified:               19047
% 27.62/3.96  sup_given_eliminated:                   12
% 27.62/3.96  comparisons_done:                       0
% 27.62/3.96  comparisons_avoided:                    0
% 27.62/3.96  
% 27.62/3.96  ------ Simplifications
% 27.62/3.96  
% 27.62/3.96  
% 27.62/3.96  sim_fw_subset_subsumed:                 6
% 27.62/3.96  sim_bw_subset_subsumed:                 0
% 27.62/3.96  sim_fw_subsumed:                        1949
% 27.62/3.96  sim_bw_subsumed:                        299
% 27.62/3.96  sim_fw_subsumption_res:                 0
% 27.62/3.96  sim_bw_subsumption_res:                 0
% 27.62/3.96  sim_tautology_del:                      0
% 27.62/3.96  sim_eq_tautology_del:                   5031
% 27.62/3.96  sim_eq_res_simp:                        34
% 27.62/3.96  sim_fw_demodulated:                     16906
% 27.62/3.96  sim_bw_demodulated:                     496
% 27.62/3.96  sim_light_normalised:                   9772
% 27.62/3.96  sim_joinable_taut:                      0
% 27.62/3.96  sim_joinable_simp:                      0
% 27.62/3.96  sim_ac_normalised:                      0
% 27.62/3.96  sim_smt_subsumption:                    0
% 27.62/3.96  
%------------------------------------------------------------------------------
