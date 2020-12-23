%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:39 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 334 expanded)
%              Number of clauses        :   34 (  51 expanded)
%              Number of leaves         :   16 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 448 expanded)
%              Number of equality atoms :   80 ( 331 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25])).

fof(f47,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f34,f51,f51,f31])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f50,f50])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f35,f31,f31,f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f36,f51,f31])).

fof(f48,plain,(
    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != sK1 ),
    inference(definition_unfolding,[],[f48,f51,f50])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_363,plain,
    ( r2_hidden(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_362,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_366,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_368,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2529,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_366,c_368])).

cnf(c_26902,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,X0)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_362,c_2529])).

cnf(c_29171,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK2) ),
    inference(superposition,[status(thm)],[c_363,c_26902])).

cnf(c_6,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29308,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2)))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_29171,c_6])).

cnf(c_4,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_791,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_4])).

cnf(c_7,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1230,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_791,c_7])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_369,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_691,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_369,c_368])).

cnf(c_1240,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1230,c_691])).

cnf(c_9,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_367,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1232,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_791,c_367])).

cnf(c_1413,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1232,c_368])).

cnf(c_8,plain,
    ( k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1068,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_691,c_8])).

cnf(c_2115,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1068,c_791])).

cnf(c_2518,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1240,c_1413,c_2115])).

cnf(c_29313,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) = sK1 ),
    inference(demodulation,[status(thm)],[c_29308,c_4,c_2518])).

cnf(c_14,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_787,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) != sK1 ),
    inference(demodulation,[status(thm)],[c_10,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29313,c_787])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:09:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.32/1.46  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/1.46  
% 7.32/1.46  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.46  
% 7.32/1.46  ------  iProver source info
% 7.32/1.46  
% 7.32/1.46  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.46  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.46  git: non_committed_changes: false
% 7.32/1.46  git: last_make_outside_of_git: false
% 7.32/1.46  
% 7.32/1.46  ------ 
% 7.32/1.46  
% 7.32/1.46  ------ Input Options
% 7.32/1.46  
% 7.32/1.46  --out_options                           all
% 7.32/1.46  --tptp_safe_out                         true
% 7.32/1.46  --problem_path                          ""
% 7.32/1.46  --include_path                          ""
% 7.32/1.46  --clausifier                            res/vclausify_rel
% 7.32/1.46  --clausifier_options                    --mode clausify
% 7.32/1.46  --stdin                                 false
% 7.32/1.46  --stats_out                             all
% 7.32/1.46  
% 7.32/1.46  ------ General Options
% 7.32/1.46  
% 7.32/1.46  --fof                                   false
% 7.32/1.46  --time_out_real                         305.
% 7.32/1.46  --time_out_virtual                      -1.
% 7.32/1.46  --symbol_type_check                     false
% 7.32/1.46  --clausify_out                          false
% 7.32/1.46  --sig_cnt_out                           false
% 7.32/1.46  --trig_cnt_out                          false
% 7.32/1.46  --trig_cnt_out_tolerance                1.
% 7.32/1.46  --trig_cnt_out_sk_spl                   false
% 7.32/1.46  --abstr_cl_out                          false
% 7.32/1.46  
% 7.32/1.46  ------ Global Options
% 7.32/1.46  
% 7.32/1.46  --schedule                              default
% 7.32/1.46  --add_important_lit                     false
% 7.32/1.46  --prop_solver_per_cl                    1000
% 7.32/1.46  --min_unsat_core                        false
% 7.32/1.46  --soft_assumptions                      false
% 7.32/1.46  --soft_lemma_size                       3
% 7.32/1.46  --prop_impl_unit_size                   0
% 7.32/1.46  --prop_impl_unit                        []
% 7.32/1.46  --share_sel_clauses                     true
% 7.32/1.46  --reset_solvers                         false
% 7.32/1.46  --bc_imp_inh                            [conj_cone]
% 7.32/1.46  --conj_cone_tolerance                   3.
% 7.32/1.46  --extra_neg_conj                        none
% 7.32/1.46  --large_theory_mode                     true
% 7.32/1.46  --prolific_symb_bound                   200
% 7.32/1.46  --lt_threshold                          2000
% 7.32/1.46  --clause_weak_htbl                      true
% 7.32/1.46  --gc_record_bc_elim                     false
% 7.32/1.46  
% 7.32/1.46  ------ Preprocessing Options
% 7.32/1.46  
% 7.32/1.46  --preprocessing_flag                    true
% 7.32/1.46  --time_out_prep_mult                    0.1
% 7.32/1.46  --splitting_mode                        input
% 7.32/1.46  --splitting_grd                         true
% 7.32/1.46  --splitting_cvd                         false
% 7.32/1.46  --splitting_cvd_svl                     false
% 7.32/1.46  --splitting_nvd                         32
% 7.32/1.46  --sub_typing                            true
% 7.32/1.46  --prep_gs_sim                           true
% 7.32/1.46  --prep_unflatten                        true
% 7.32/1.46  --prep_res_sim                          true
% 7.32/1.46  --prep_upred                            true
% 7.32/1.46  --prep_sem_filter                       exhaustive
% 7.32/1.46  --prep_sem_filter_out                   false
% 7.32/1.46  --pred_elim                             true
% 7.32/1.46  --res_sim_input                         true
% 7.32/1.46  --eq_ax_congr_red                       true
% 7.32/1.46  --pure_diseq_elim                       true
% 7.32/1.46  --brand_transform                       false
% 7.32/1.46  --non_eq_to_eq                          false
% 7.32/1.46  --prep_def_merge                        true
% 7.32/1.46  --prep_def_merge_prop_impl              false
% 7.32/1.46  --prep_def_merge_mbd                    true
% 7.32/1.46  --prep_def_merge_tr_red                 false
% 7.32/1.46  --prep_def_merge_tr_cl                  false
% 7.32/1.46  --smt_preprocessing                     true
% 7.32/1.46  --smt_ac_axioms                         fast
% 7.32/1.46  --preprocessed_out                      false
% 7.32/1.46  --preprocessed_stats                    false
% 7.32/1.46  
% 7.32/1.46  ------ Abstraction refinement Options
% 7.32/1.46  
% 7.32/1.46  --abstr_ref                             []
% 7.32/1.46  --abstr_ref_prep                        false
% 7.32/1.46  --abstr_ref_until_sat                   false
% 7.32/1.46  --abstr_ref_sig_restrict                funpre
% 7.32/1.46  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.46  --abstr_ref_under                       []
% 7.32/1.46  
% 7.32/1.46  ------ SAT Options
% 7.32/1.46  
% 7.32/1.46  --sat_mode                              false
% 7.32/1.46  --sat_fm_restart_options                ""
% 7.32/1.46  --sat_gr_def                            false
% 7.32/1.46  --sat_epr_types                         true
% 7.32/1.46  --sat_non_cyclic_types                  false
% 7.32/1.46  --sat_finite_models                     false
% 7.32/1.46  --sat_fm_lemmas                         false
% 7.32/1.46  --sat_fm_prep                           false
% 7.32/1.46  --sat_fm_uc_incr                        true
% 7.32/1.46  --sat_out_model                         small
% 7.32/1.46  --sat_out_clauses                       false
% 7.32/1.46  
% 7.32/1.46  ------ QBF Options
% 7.32/1.46  
% 7.32/1.46  --qbf_mode                              false
% 7.32/1.46  --qbf_elim_univ                         false
% 7.32/1.46  --qbf_dom_inst                          none
% 7.32/1.46  --qbf_dom_pre_inst                      false
% 7.32/1.46  --qbf_sk_in                             false
% 7.32/1.46  --qbf_pred_elim                         true
% 7.32/1.46  --qbf_split                             512
% 7.32/1.46  
% 7.32/1.46  ------ BMC1 Options
% 7.32/1.46  
% 7.32/1.46  --bmc1_incremental                      false
% 7.32/1.46  --bmc1_axioms                           reachable_all
% 7.32/1.46  --bmc1_min_bound                        0
% 7.32/1.46  --bmc1_max_bound                        -1
% 7.32/1.46  --bmc1_max_bound_default                -1
% 7.32/1.46  --bmc1_symbol_reachability              true
% 7.32/1.46  --bmc1_property_lemmas                  false
% 7.32/1.46  --bmc1_k_induction                      false
% 7.32/1.46  --bmc1_non_equiv_states                 false
% 7.32/1.46  --bmc1_deadlock                         false
% 7.32/1.46  --bmc1_ucm                              false
% 7.32/1.46  --bmc1_add_unsat_core                   none
% 7.32/1.46  --bmc1_unsat_core_children              false
% 7.32/1.46  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.46  --bmc1_out_stat                         full
% 7.32/1.46  --bmc1_ground_init                      false
% 7.32/1.46  --bmc1_pre_inst_next_state              false
% 7.32/1.46  --bmc1_pre_inst_state                   false
% 7.32/1.46  --bmc1_pre_inst_reach_state             false
% 7.32/1.46  --bmc1_out_unsat_core                   false
% 7.32/1.46  --bmc1_aig_witness_out                  false
% 7.32/1.46  --bmc1_verbose                          false
% 7.32/1.46  --bmc1_dump_clauses_tptp                false
% 7.32/1.46  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.46  --bmc1_dump_file                        -
% 7.32/1.46  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.46  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.46  --bmc1_ucm_extend_mode                  1
% 7.32/1.46  --bmc1_ucm_init_mode                    2
% 7.32/1.46  --bmc1_ucm_cone_mode                    none
% 7.32/1.46  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.46  --bmc1_ucm_relax_model                  4
% 7.32/1.46  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.46  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.46  --bmc1_ucm_layered_model                none
% 7.32/1.46  --bmc1_ucm_max_lemma_size               10
% 7.32/1.46  
% 7.32/1.46  ------ AIG Options
% 7.32/1.46  
% 7.32/1.46  --aig_mode                              false
% 7.32/1.46  
% 7.32/1.46  ------ Instantiation Options
% 7.32/1.46  
% 7.32/1.46  --instantiation_flag                    true
% 7.32/1.46  --inst_sos_flag                         false
% 7.32/1.46  --inst_sos_phase                        true
% 7.32/1.46  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.46  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.46  --inst_lit_sel_side                     num_symb
% 7.32/1.46  --inst_solver_per_active                1400
% 7.32/1.46  --inst_solver_calls_frac                1.
% 7.32/1.46  --inst_passive_queue_type               priority_queues
% 7.32/1.46  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.46  --inst_passive_queues_freq              [25;2]
% 7.32/1.46  --inst_dismatching                      true
% 7.32/1.46  --inst_eager_unprocessed_to_passive     true
% 7.32/1.46  --inst_prop_sim_given                   true
% 7.32/1.46  --inst_prop_sim_new                     false
% 7.32/1.46  --inst_subs_new                         false
% 7.32/1.46  --inst_eq_res_simp                      false
% 7.32/1.46  --inst_subs_given                       false
% 7.32/1.46  --inst_orphan_elimination               true
% 7.32/1.46  --inst_learning_loop_flag               true
% 7.32/1.46  --inst_learning_start                   3000
% 7.32/1.46  --inst_learning_factor                  2
% 7.32/1.46  --inst_start_prop_sim_after_learn       3
% 7.32/1.46  --inst_sel_renew                        solver
% 7.32/1.46  --inst_lit_activity_flag                true
% 7.32/1.46  --inst_restr_to_given                   false
% 7.32/1.46  --inst_activity_threshold               500
% 7.32/1.46  --inst_out_proof                        true
% 7.32/1.46  
% 7.32/1.46  ------ Resolution Options
% 7.32/1.46  
% 7.32/1.46  --resolution_flag                       true
% 7.32/1.46  --res_lit_sel                           adaptive
% 7.32/1.46  --res_lit_sel_side                      none
% 7.32/1.46  --res_ordering                          kbo
% 7.32/1.46  --res_to_prop_solver                    active
% 7.32/1.46  --res_prop_simpl_new                    false
% 7.32/1.46  --res_prop_simpl_given                  true
% 7.32/1.46  --res_passive_queue_type                priority_queues
% 7.32/1.46  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.46  --res_passive_queues_freq               [15;5]
% 7.32/1.46  --res_forward_subs                      full
% 7.32/1.46  --res_backward_subs                     full
% 7.32/1.46  --res_forward_subs_resolution           true
% 7.32/1.46  --res_backward_subs_resolution          true
% 7.32/1.46  --res_orphan_elimination                true
% 7.32/1.46  --res_time_limit                        2.
% 7.32/1.46  --res_out_proof                         true
% 7.32/1.46  
% 7.32/1.46  ------ Superposition Options
% 7.32/1.46  
% 7.32/1.46  --superposition_flag                    true
% 7.32/1.46  --sup_passive_queue_type                priority_queues
% 7.32/1.46  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.46  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.46  --demod_completeness_check              fast
% 7.32/1.46  --demod_use_ground                      true
% 7.32/1.46  --sup_to_prop_solver                    passive
% 7.32/1.46  --sup_prop_simpl_new                    true
% 7.32/1.46  --sup_prop_simpl_given                  true
% 7.32/1.46  --sup_fun_splitting                     false
% 7.32/1.46  --sup_smt_interval                      50000
% 7.32/1.46  
% 7.32/1.46  ------ Superposition Simplification Setup
% 7.32/1.46  
% 7.32/1.46  --sup_indices_passive                   []
% 7.32/1.46  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.46  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.46  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.46  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.46  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.46  --sup_full_bw                           [BwDemod]
% 7.32/1.46  --sup_immed_triv                        [TrivRules]
% 7.32/1.46  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.46  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.46  --sup_immed_bw_main                     []
% 7.32/1.46  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.46  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.46  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.46  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.46  
% 7.32/1.46  ------ Combination Options
% 7.32/1.46  
% 7.32/1.46  --comb_res_mult                         3
% 7.32/1.46  --comb_sup_mult                         2
% 7.32/1.46  --comb_inst_mult                        10
% 7.32/1.46  
% 7.32/1.46  ------ Debug Options
% 7.32/1.46  
% 7.32/1.46  --dbg_backtrace                         false
% 7.32/1.46  --dbg_dump_prop_clauses                 false
% 7.32/1.46  --dbg_dump_prop_clauses_file            -
% 7.32/1.46  --dbg_out_stat                          false
% 7.32/1.46  ------ Parsing...
% 7.32/1.46  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.46  
% 7.32/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.32/1.46  
% 7.32/1.46  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.46  
% 7.32/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.46  ------ Proving...
% 7.32/1.46  ------ Problem Properties 
% 7.32/1.46  
% 7.32/1.46  
% 7.32/1.46  clauses                                 16
% 7.32/1.46  conjectures                             3
% 7.32/1.46  EPR                                     4
% 7.32/1.46  Horn                                    16
% 7.32/1.46  unary                                   11
% 7.32/1.46  binary                                  3
% 7.32/1.46  lits                                    23
% 7.32/1.46  lits eq                                 9
% 7.32/1.46  fd_pure                                 0
% 7.32/1.46  fd_pseudo                               0
% 7.32/1.46  fd_cond                                 0
% 7.32/1.46  fd_pseudo_cond                          1
% 7.32/1.46  AC symbols                              0
% 7.32/1.46  
% 7.32/1.46  ------ Schedule dynamic 5 is on 
% 7.32/1.46  
% 7.32/1.46  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.32/1.46  
% 7.32/1.46  
% 7.32/1.46  ------ 
% 7.32/1.46  Current options:
% 7.32/1.46  ------ 
% 7.32/1.46  
% 7.32/1.46  ------ Input Options
% 7.32/1.46  
% 7.32/1.46  --out_options                           all
% 7.32/1.46  --tptp_safe_out                         true
% 7.32/1.46  --problem_path                          ""
% 7.32/1.46  --include_path                          ""
% 7.32/1.46  --clausifier                            res/vclausify_rel
% 7.32/1.46  --clausifier_options                    --mode clausify
% 7.32/1.46  --stdin                                 false
% 7.32/1.46  --stats_out                             all
% 7.32/1.46  
% 7.32/1.46  ------ General Options
% 7.32/1.46  
% 7.32/1.46  --fof                                   false
% 7.32/1.46  --time_out_real                         305.
% 7.32/1.46  --time_out_virtual                      -1.
% 7.32/1.46  --symbol_type_check                     false
% 7.32/1.46  --clausify_out                          false
% 7.32/1.46  --sig_cnt_out                           false
% 7.32/1.46  --trig_cnt_out                          false
% 7.32/1.46  --trig_cnt_out_tolerance                1.
% 7.32/1.46  --trig_cnt_out_sk_spl                   false
% 7.32/1.46  --abstr_cl_out                          false
% 7.32/1.46  
% 7.32/1.46  ------ Global Options
% 7.32/1.46  
% 7.32/1.46  --schedule                              default
% 7.32/1.46  --add_important_lit                     false
% 7.32/1.46  --prop_solver_per_cl                    1000
% 7.32/1.46  --min_unsat_core                        false
% 7.32/1.46  --soft_assumptions                      false
% 7.32/1.46  --soft_lemma_size                       3
% 7.32/1.46  --prop_impl_unit_size                   0
% 7.32/1.46  --prop_impl_unit                        []
% 7.32/1.46  --share_sel_clauses                     true
% 7.32/1.46  --reset_solvers                         false
% 7.32/1.46  --bc_imp_inh                            [conj_cone]
% 7.32/1.46  --conj_cone_tolerance                   3.
% 7.32/1.46  --extra_neg_conj                        none
% 7.32/1.46  --large_theory_mode                     true
% 7.32/1.46  --prolific_symb_bound                   200
% 7.32/1.46  --lt_threshold                          2000
% 7.32/1.46  --clause_weak_htbl                      true
% 7.32/1.46  --gc_record_bc_elim                     false
% 7.32/1.46  
% 7.32/1.46  ------ Preprocessing Options
% 7.32/1.46  
% 7.32/1.46  --preprocessing_flag                    true
% 7.32/1.46  --time_out_prep_mult                    0.1
% 7.32/1.46  --splitting_mode                        input
% 7.32/1.46  --splitting_grd                         true
% 7.32/1.46  --splitting_cvd                         false
% 7.32/1.46  --splitting_cvd_svl                     false
% 7.32/1.46  --splitting_nvd                         32
% 7.32/1.46  --sub_typing                            true
% 7.32/1.46  --prep_gs_sim                           true
% 7.32/1.46  --prep_unflatten                        true
% 7.32/1.46  --prep_res_sim                          true
% 7.32/1.46  --prep_upred                            true
% 7.32/1.46  --prep_sem_filter                       exhaustive
% 7.32/1.46  --prep_sem_filter_out                   false
% 7.32/1.46  --pred_elim                             true
% 7.32/1.46  --res_sim_input                         true
% 7.32/1.46  --eq_ax_congr_red                       true
% 7.32/1.46  --pure_diseq_elim                       true
% 7.32/1.46  --brand_transform                       false
% 7.32/1.46  --non_eq_to_eq                          false
% 7.32/1.46  --prep_def_merge                        true
% 7.32/1.46  --prep_def_merge_prop_impl              false
% 7.32/1.46  --prep_def_merge_mbd                    true
% 7.32/1.46  --prep_def_merge_tr_red                 false
% 7.32/1.46  --prep_def_merge_tr_cl                  false
% 7.32/1.46  --smt_preprocessing                     true
% 7.32/1.46  --smt_ac_axioms                         fast
% 7.32/1.46  --preprocessed_out                      false
% 7.32/1.46  --preprocessed_stats                    false
% 7.32/1.46  
% 7.32/1.46  ------ Abstraction refinement Options
% 7.32/1.46  
% 7.32/1.46  --abstr_ref                             []
% 7.32/1.46  --abstr_ref_prep                        false
% 7.32/1.46  --abstr_ref_until_sat                   false
% 7.32/1.46  --abstr_ref_sig_restrict                funpre
% 7.32/1.46  --abstr_ref_af_restrict_to_split_sk     false
% 7.32/1.46  --abstr_ref_under                       []
% 7.32/1.46  
% 7.32/1.46  ------ SAT Options
% 7.32/1.46  
% 7.32/1.46  --sat_mode                              false
% 7.32/1.46  --sat_fm_restart_options                ""
% 7.32/1.46  --sat_gr_def                            false
% 7.32/1.46  --sat_epr_types                         true
% 7.32/1.46  --sat_non_cyclic_types                  false
% 7.32/1.46  --sat_finite_models                     false
% 7.32/1.46  --sat_fm_lemmas                         false
% 7.32/1.46  --sat_fm_prep                           false
% 7.32/1.46  --sat_fm_uc_incr                        true
% 7.32/1.46  --sat_out_model                         small
% 7.32/1.46  --sat_out_clauses                       false
% 7.32/1.46  
% 7.32/1.46  ------ QBF Options
% 7.32/1.46  
% 7.32/1.46  --qbf_mode                              false
% 7.32/1.46  --qbf_elim_univ                         false
% 7.32/1.46  --qbf_dom_inst                          none
% 7.32/1.46  --qbf_dom_pre_inst                      false
% 7.32/1.46  --qbf_sk_in                             false
% 7.32/1.46  --qbf_pred_elim                         true
% 7.32/1.46  --qbf_split                             512
% 7.32/1.46  
% 7.32/1.46  ------ BMC1 Options
% 7.32/1.46  
% 7.32/1.46  --bmc1_incremental                      false
% 7.32/1.46  --bmc1_axioms                           reachable_all
% 7.32/1.46  --bmc1_min_bound                        0
% 7.32/1.46  --bmc1_max_bound                        -1
% 7.32/1.46  --bmc1_max_bound_default                -1
% 7.32/1.46  --bmc1_symbol_reachability              true
% 7.32/1.46  --bmc1_property_lemmas                  false
% 7.32/1.46  --bmc1_k_induction                      false
% 7.32/1.46  --bmc1_non_equiv_states                 false
% 7.32/1.46  --bmc1_deadlock                         false
% 7.32/1.46  --bmc1_ucm                              false
% 7.32/1.46  --bmc1_add_unsat_core                   none
% 7.32/1.46  --bmc1_unsat_core_children              false
% 7.32/1.46  --bmc1_unsat_core_extrapolate_axioms    false
% 7.32/1.46  --bmc1_out_stat                         full
% 7.32/1.46  --bmc1_ground_init                      false
% 7.32/1.46  --bmc1_pre_inst_next_state              false
% 7.32/1.46  --bmc1_pre_inst_state                   false
% 7.32/1.46  --bmc1_pre_inst_reach_state             false
% 7.32/1.46  --bmc1_out_unsat_core                   false
% 7.32/1.46  --bmc1_aig_witness_out                  false
% 7.32/1.46  --bmc1_verbose                          false
% 7.32/1.46  --bmc1_dump_clauses_tptp                false
% 7.32/1.46  --bmc1_dump_unsat_core_tptp             false
% 7.32/1.46  --bmc1_dump_file                        -
% 7.32/1.46  --bmc1_ucm_expand_uc_limit              128
% 7.32/1.46  --bmc1_ucm_n_expand_iterations          6
% 7.32/1.46  --bmc1_ucm_extend_mode                  1
% 7.32/1.46  --bmc1_ucm_init_mode                    2
% 7.32/1.46  --bmc1_ucm_cone_mode                    none
% 7.32/1.46  --bmc1_ucm_reduced_relation_type        0
% 7.32/1.46  --bmc1_ucm_relax_model                  4
% 7.32/1.46  --bmc1_ucm_full_tr_after_sat            true
% 7.32/1.46  --bmc1_ucm_expand_neg_assumptions       false
% 7.32/1.46  --bmc1_ucm_layered_model                none
% 7.32/1.46  --bmc1_ucm_max_lemma_size               10
% 7.32/1.46  
% 7.32/1.46  ------ AIG Options
% 7.32/1.46  
% 7.32/1.46  --aig_mode                              false
% 7.32/1.46  
% 7.32/1.46  ------ Instantiation Options
% 7.32/1.46  
% 7.32/1.46  --instantiation_flag                    true
% 7.32/1.46  --inst_sos_flag                         false
% 7.32/1.46  --inst_sos_phase                        true
% 7.32/1.46  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.32/1.46  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.32/1.46  --inst_lit_sel_side                     none
% 7.32/1.46  --inst_solver_per_active                1400
% 7.32/1.46  --inst_solver_calls_frac                1.
% 7.32/1.46  --inst_passive_queue_type               priority_queues
% 7.32/1.46  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.32/1.46  --inst_passive_queues_freq              [25;2]
% 7.32/1.46  --inst_dismatching                      true
% 7.32/1.46  --inst_eager_unprocessed_to_passive     true
% 7.32/1.46  --inst_prop_sim_given                   true
% 7.32/1.46  --inst_prop_sim_new                     false
% 7.32/1.46  --inst_subs_new                         false
% 7.32/1.46  --inst_eq_res_simp                      false
% 7.32/1.46  --inst_subs_given                       false
% 7.32/1.46  --inst_orphan_elimination               true
% 7.32/1.46  --inst_learning_loop_flag               true
% 7.32/1.46  --inst_learning_start                   3000
% 7.32/1.46  --inst_learning_factor                  2
% 7.32/1.46  --inst_start_prop_sim_after_learn       3
% 7.32/1.46  --inst_sel_renew                        solver
% 7.32/1.46  --inst_lit_activity_flag                true
% 7.32/1.46  --inst_restr_to_given                   false
% 7.32/1.46  --inst_activity_threshold               500
% 7.32/1.46  --inst_out_proof                        true
% 7.32/1.46  
% 7.32/1.46  ------ Resolution Options
% 7.32/1.46  
% 7.32/1.46  --resolution_flag                       false
% 7.32/1.46  --res_lit_sel                           adaptive
% 7.32/1.46  --res_lit_sel_side                      none
% 7.32/1.46  --res_ordering                          kbo
% 7.32/1.46  --res_to_prop_solver                    active
% 7.32/1.46  --res_prop_simpl_new                    false
% 7.32/1.46  --res_prop_simpl_given                  true
% 7.32/1.46  --res_passive_queue_type                priority_queues
% 7.32/1.46  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.32/1.46  --res_passive_queues_freq               [15;5]
% 7.32/1.46  --res_forward_subs                      full
% 7.32/1.46  --res_backward_subs                     full
% 7.32/1.46  --res_forward_subs_resolution           true
% 7.32/1.46  --res_backward_subs_resolution          true
% 7.32/1.46  --res_orphan_elimination                true
% 7.32/1.46  --res_time_limit                        2.
% 7.32/1.46  --res_out_proof                         true
% 7.32/1.46  
% 7.32/1.46  ------ Superposition Options
% 7.32/1.46  
% 7.32/1.46  --superposition_flag                    true
% 7.32/1.46  --sup_passive_queue_type                priority_queues
% 7.32/1.46  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.32/1.46  --sup_passive_queues_freq               [8;1;4]
% 7.32/1.46  --demod_completeness_check              fast
% 7.32/1.46  --demod_use_ground                      true
% 7.32/1.46  --sup_to_prop_solver                    passive
% 7.32/1.46  --sup_prop_simpl_new                    true
% 7.32/1.46  --sup_prop_simpl_given                  true
% 7.32/1.46  --sup_fun_splitting                     false
% 7.32/1.46  --sup_smt_interval                      50000
% 7.32/1.46  
% 7.32/1.46  ------ Superposition Simplification Setup
% 7.32/1.46  
% 7.32/1.46  --sup_indices_passive                   []
% 7.32/1.46  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.46  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.46  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.32/1.46  --sup_full_triv                         [TrivRules;PropSubs]
% 7.32/1.46  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.46  --sup_full_bw                           [BwDemod]
% 7.32/1.46  --sup_immed_triv                        [TrivRules]
% 7.32/1.46  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.32/1.46  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.46  --sup_immed_bw_main                     []
% 7.32/1.46  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.46  --sup_input_triv                        [Unflattening;TrivRules]
% 7.32/1.46  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.32/1.46  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.32/1.46  
% 7.32/1.46  ------ Combination Options
% 7.32/1.46  
% 7.32/1.46  --comb_res_mult                         3
% 7.32/1.46  --comb_sup_mult                         2
% 7.32/1.46  --comb_inst_mult                        10
% 7.32/1.46  
% 7.32/1.46  ------ Debug Options
% 7.32/1.46  
% 7.32/1.46  --dbg_backtrace                         false
% 7.32/1.46  --dbg_dump_prop_clauses                 false
% 7.32/1.46  --dbg_dump_prop_clauses_file            -
% 7.32/1.46  --dbg_out_stat                          false
% 7.32/1.46  
% 7.32/1.46  
% 7.32/1.46  
% 7.32/1.46  
% 7.32/1.46  ------ Proving...
% 7.32/1.46  
% 7.32/1.46  
% 7.32/1.46  % SZS status Theorem for theBenchmark.p
% 7.32/1.46  
% 7.32/1.46  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.46  
% 7.32/1.46  fof(f16,conjecture,(
% 7.32/1.46    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f17,negated_conjecture,(
% 7.32/1.46    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 7.32/1.46    inference(negated_conjecture,[],[f16])).
% 7.32/1.46  
% 7.32/1.46  fof(f19,plain,(
% 7.32/1.46    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 7.32/1.46    inference(ennf_transformation,[],[f17])).
% 7.32/1.46  
% 7.32/1.46  fof(f20,plain,(
% 7.32/1.46    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 7.32/1.46    inference(flattening,[],[f19])).
% 7.32/1.46  
% 7.32/1.46  fof(f25,plain,(
% 7.32/1.46    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 7.32/1.46    introduced(choice_axiom,[])).
% 7.32/1.46  
% 7.32/1.46  fof(f26,plain,(
% 7.32/1.46    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1 & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 7.32/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25])).
% 7.32/1.46  
% 7.32/1.46  fof(f47,plain,(
% 7.32/1.46    r2_hidden(sK2,sK1)),
% 7.32/1.46    inference(cnf_transformation,[],[f26])).
% 7.32/1.46  
% 7.32/1.46  fof(f46,plain,(
% 7.32/1.46    r2_hidden(sK0,sK1)),
% 7.32/1.46    inference(cnf_transformation,[],[f26])).
% 7.32/1.46  
% 7.32/1.46  fof(f15,axiom,(
% 7.32/1.46    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f23,plain,(
% 7.32/1.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.32/1.46    inference(nnf_transformation,[],[f15])).
% 7.32/1.46  
% 7.32/1.46  fof(f24,plain,(
% 7.32/1.46    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 7.32/1.46    inference(flattening,[],[f23])).
% 7.32/1.46  
% 7.32/1.46  fof(f45,plain,(
% 7.32/1.46    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.32/1.46    inference(cnf_transformation,[],[f24])).
% 7.32/1.46  
% 7.32/1.46  fof(f11,axiom,(
% 7.32/1.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f39,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.32/1.46    inference(cnf_transformation,[],[f11])).
% 7.32/1.46  
% 7.32/1.46  fof(f12,axiom,(
% 7.32/1.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f40,plain,(
% 7.32/1.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.32/1.46    inference(cnf_transformation,[],[f12])).
% 7.32/1.46  
% 7.32/1.46  fof(f13,axiom,(
% 7.32/1.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f41,plain,(
% 7.32/1.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.32/1.46    inference(cnf_transformation,[],[f13])).
% 7.32/1.46  
% 7.32/1.46  fof(f49,plain,(
% 7.32/1.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.32/1.46    inference(definition_unfolding,[],[f40,f41])).
% 7.32/1.46  
% 7.32/1.46  fof(f50,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.32/1.46    inference(definition_unfolding,[],[f39,f49])).
% 7.32/1.46  
% 7.32/1.46  fof(f58,plain,(
% 7.32/1.46    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.32/1.46    inference(definition_unfolding,[],[f45,f50])).
% 7.32/1.46  
% 7.32/1.46  fof(f5,axiom,(
% 7.32/1.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f18,plain,(
% 7.32/1.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.32/1.46    inference(ennf_transformation,[],[f5])).
% 7.32/1.46  
% 7.32/1.46  fof(f33,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.32/1.46    inference(cnf_transformation,[],[f18])).
% 7.32/1.46  
% 7.32/1.46  fof(f6,axiom,(
% 7.32/1.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f34,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.32/1.46    inference(cnf_transformation,[],[f6])).
% 7.32/1.46  
% 7.32/1.46  fof(f14,axiom,(
% 7.32/1.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f42,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.32/1.46    inference(cnf_transformation,[],[f14])).
% 7.32/1.46  
% 7.32/1.46  fof(f51,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 7.32/1.46    inference(definition_unfolding,[],[f42,f50])).
% 7.32/1.46  
% 7.32/1.46  fof(f3,axiom,(
% 7.32/1.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f31,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.32/1.46    inference(cnf_transformation,[],[f3])).
% 7.32/1.46  
% 7.32/1.46  fof(f53,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 7.32/1.46    inference(definition_unfolding,[],[f34,f51,f51,f31])).
% 7.32/1.46  
% 7.32/1.46  fof(f4,axiom,(
% 7.32/1.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f32,plain,(
% 7.32/1.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.32/1.46    inference(cnf_transformation,[],[f4])).
% 7.32/1.46  
% 7.32/1.46  fof(f52,plain,(
% 7.32/1.46    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 7.32/1.46    inference(definition_unfolding,[],[f32,f51])).
% 7.32/1.46  
% 7.32/1.46  fof(f10,axiom,(
% 7.32/1.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f38,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.32/1.46    inference(cnf_transformation,[],[f10])).
% 7.32/1.46  
% 7.32/1.46  fof(f57,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 7.32/1.46    inference(definition_unfolding,[],[f38,f50,f50])).
% 7.32/1.46  
% 7.32/1.46  fof(f7,axiom,(
% 7.32/1.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f35,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.32/1.46    inference(cnf_transformation,[],[f7])).
% 7.32/1.46  
% 7.32/1.46  fof(f54,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 7.32/1.46    inference(definition_unfolding,[],[f35,f31,f31,f51])).
% 7.32/1.46  
% 7.32/1.46  fof(f2,axiom,(
% 7.32/1.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f21,plain,(
% 7.32/1.46    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.32/1.46    inference(nnf_transformation,[],[f2])).
% 7.32/1.46  
% 7.32/1.46  fof(f22,plain,(
% 7.32/1.46    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.32/1.46    inference(flattening,[],[f21])).
% 7.32/1.46  
% 7.32/1.46  fof(f28,plain,(
% 7.32/1.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.32/1.46    inference(cnf_transformation,[],[f22])).
% 7.32/1.46  
% 7.32/1.46  fof(f63,plain,(
% 7.32/1.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.32/1.46    inference(equality_resolution,[],[f28])).
% 7.32/1.46  
% 7.32/1.46  fof(f9,axiom,(
% 7.32/1.46    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f37,plain,(
% 7.32/1.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.32/1.46    inference(cnf_transformation,[],[f9])).
% 7.32/1.46  
% 7.32/1.46  fof(f56,plain,(
% 7.32/1.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 7.32/1.46    inference(definition_unfolding,[],[f37,f51])).
% 7.32/1.46  
% 7.32/1.46  fof(f8,axiom,(
% 7.32/1.46    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.32/1.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.46  
% 7.32/1.46  fof(f36,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.32/1.46    inference(cnf_transformation,[],[f8])).
% 7.32/1.46  
% 7.32/1.46  fof(f55,plain,(
% 7.32/1.46    ( ! [X0,X1] : (k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 7.32/1.46    inference(definition_unfolding,[],[f36,f51,f31])).
% 7.32/1.46  
% 7.32/1.46  fof(f48,plain,(
% 7.32/1.46    k2_xboole_0(k2_tarski(sK0,sK2),sK1) != sK1),
% 7.32/1.46    inference(cnf_transformation,[],[f26])).
% 7.32/1.46  
% 7.32/1.46  fof(f61,plain,(
% 7.32/1.46    k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != sK1),
% 7.32/1.46    inference(definition_unfolding,[],[f48,f51,f50])).
% 7.32/1.46  
% 7.32/1.46  cnf(c_15,negated_conjecture,
% 7.32/1.46      ( r2_hidden(sK2,sK1) ),
% 7.32/1.46      inference(cnf_transformation,[],[f47]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_363,plain,
% 7.32/1.46      ( r2_hidden(sK2,sK1) = iProver_top ),
% 7.32/1.46      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_16,negated_conjecture,
% 7.32/1.46      ( r2_hidden(sK0,sK1) ),
% 7.32/1.46      inference(cnf_transformation,[],[f46]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_362,plain,
% 7.32/1.46      ( r2_hidden(sK0,sK1) = iProver_top ),
% 7.32/1.46      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_11,plain,
% 7.32/1.46      ( ~ r2_hidden(X0,X1)
% 7.32/1.46      | ~ r2_hidden(X2,X1)
% 7.32/1.46      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 7.32/1.46      inference(cnf_transformation,[],[f58]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_366,plain,
% 7.32/1.46      ( r2_hidden(X0,X1) != iProver_top
% 7.32/1.46      | r2_hidden(X2,X1) != iProver_top
% 7.32/1.46      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
% 7.32/1.46      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_5,plain,
% 7.32/1.46      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.32/1.46      inference(cnf_transformation,[],[f33]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_368,plain,
% 7.32/1.46      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.32/1.46      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_2529,plain,
% 7.32/1.46      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 7.32/1.46      | r2_hidden(X1,X2) != iProver_top
% 7.32/1.46      | r2_hidden(X0,X2) != iProver_top ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_366,c_368]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_26902,plain,
% 7.32/1.46      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,X0)
% 7.32/1.46      | r2_hidden(X0,sK1) != iProver_top ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_362,c_2529]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_29171,plain,
% 7.32/1.46      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK2) ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_363,c_26902]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_6,plain,
% 7.32/1.46      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 7.32/1.46      inference(cnf_transformation,[],[f53]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_29308,plain,
% 7.32/1.46      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2)))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_29171,c_6]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_4,plain,
% 7.32/1.46      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 7.32/1.46      inference(cnf_transformation,[],[f52]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_10,plain,
% 7.32/1.46      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 7.32/1.46      inference(cnf_transformation,[],[f57]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_791,plain,
% 7.32/1.46      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_10,c_4]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_7,plain,
% 7.32/1.46      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.32/1.46      inference(cnf_transformation,[],[f54]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_1230,plain,
% 7.32/1.46      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_791,c_7]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_3,plain,
% 7.32/1.46      ( r1_tarski(X0,X0) ),
% 7.32/1.46      inference(cnf_transformation,[],[f63]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_369,plain,
% 7.32/1.46      ( r1_tarski(X0,X0) = iProver_top ),
% 7.32/1.46      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_691,plain,
% 7.32/1.46      ( k3_xboole_0(X0,X0) = X0 ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_369,c_368]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_1240,plain,
% 7.32/1.46      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,X0) ),
% 7.32/1.46      inference(light_normalisation,[status(thm)],[c_1230,c_691]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_9,plain,
% 7.32/1.46      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 7.32/1.46      inference(cnf_transformation,[],[f56]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_367,plain,
% 7.32/1.46      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 7.32/1.46      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_1232,plain,
% 7.32/1.46      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_791,c_367]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_1413,plain,
% 7.32/1.46      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_1232,c_368]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_8,plain,
% 7.32/1.46      ( k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 7.32/1.46      inference(cnf_transformation,[],[f55]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_1068,plain,
% 7.32/1.46      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X0,X0))) = X0 ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_691,c_8]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_2115,plain,
% 7.32/1.46      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.32/1.46      inference(superposition,[status(thm)],[c_1068,c_791]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_2518,plain,
% 7.32/1.46      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.32/1.46      inference(light_normalisation,[status(thm)],[c_1240,c_1413,c_2115]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_29313,plain,
% 7.32/1.46      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) = sK1 ),
% 7.32/1.46      inference(demodulation,[status(thm)],[c_29308,c_4,c_2518]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_14,negated_conjecture,
% 7.32/1.46      ( k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK2),sK1)) != sK1 ),
% 7.32/1.46      inference(cnf_transformation,[],[f61]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(c_787,plain,
% 7.32/1.46      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) != sK1 ),
% 7.32/1.46      inference(demodulation,[status(thm)],[c_10,c_14]) ).
% 7.32/1.46  
% 7.32/1.46  cnf(contradiction,plain,
% 7.32/1.46      ( $false ),
% 7.32/1.46      inference(minisat,[status(thm)],[c_29313,c_787]) ).
% 7.32/1.46  
% 7.32/1.46  
% 7.32/1.46  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.46  
% 7.32/1.46  ------                               Statistics
% 7.32/1.46  
% 7.32/1.46  ------ General
% 7.32/1.46  
% 7.32/1.46  abstr_ref_over_cycles:                  0
% 7.32/1.46  abstr_ref_under_cycles:                 0
% 7.32/1.46  gc_basic_clause_elim:                   0
% 7.32/1.46  forced_gc_time:                         0
% 7.32/1.46  parsing_time:                           0.007
% 7.32/1.46  unif_index_cands_time:                  0.
% 7.32/1.46  unif_index_add_time:                    0.
% 7.32/1.46  orderings_time:                         0.
% 7.32/1.46  out_proof_time:                         0.007
% 7.32/1.46  total_time:                             0.736
% 7.32/1.46  num_of_symbols:                         41
% 7.32/1.46  num_of_terms:                           29427
% 7.32/1.46  
% 7.32/1.46  ------ Preprocessing
% 7.32/1.46  
% 7.32/1.46  num_of_splits:                          0
% 7.32/1.46  num_of_split_atoms:                     0
% 7.32/1.46  num_of_reused_defs:                     0
% 7.32/1.46  num_eq_ax_congr_red:                    3
% 7.32/1.46  num_of_sem_filtered_clauses:            1
% 7.32/1.46  num_of_subtypes:                        0
% 7.32/1.46  monotx_restored_types:                  0
% 7.32/1.46  sat_num_of_epr_types:                   0
% 7.32/1.46  sat_num_of_non_cyclic_types:            0
% 7.32/1.46  sat_guarded_non_collapsed_types:        0
% 7.32/1.46  num_pure_diseq_elim:                    0
% 7.32/1.46  simp_replaced_by:                       0
% 7.32/1.46  res_preprocessed:                       81
% 7.32/1.46  prep_upred:                             0
% 7.32/1.46  prep_unflattend:                        0
% 7.32/1.46  smt_new_axioms:                         0
% 7.32/1.46  pred_elim_cands:                        2
% 7.32/1.46  pred_elim:                              0
% 7.32/1.46  pred_elim_cl:                           0
% 7.32/1.46  pred_elim_cycles:                       2
% 7.32/1.46  merged_defs:                            0
% 7.32/1.46  merged_defs_ncl:                        0
% 7.32/1.46  bin_hyper_res:                          0
% 7.32/1.46  prep_cycles:                            4
% 7.32/1.46  pred_elim_time:                         0.
% 7.32/1.46  splitting_time:                         0.
% 7.32/1.46  sem_filter_time:                        0.
% 7.32/1.46  monotx_time:                            0.
% 7.32/1.46  subtype_inf_time:                       0.
% 7.32/1.46  
% 7.32/1.46  ------ Problem properties
% 7.32/1.46  
% 7.32/1.46  clauses:                                16
% 7.32/1.46  conjectures:                            3
% 7.32/1.46  epr:                                    4
% 7.32/1.46  horn:                                   16
% 7.32/1.46  ground:                                 3
% 7.32/1.46  unary:                                  11
% 7.32/1.46  binary:                                 3
% 7.32/1.46  lits:                                   23
% 7.32/1.46  lits_eq:                                9
% 7.32/1.46  fd_pure:                                0
% 7.32/1.46  fd_pseudo:                              0
% 7.32/1.46  fd_cond:                                0
% 7.32/1.46  fd_pseudo_cond:                         1
% 7.32/1.46  ac_symbols:                             0
% 7.32/1.46  
% 7.32/1.46  ------ Propositional Solver
% 7.32/1.46  
% 7.32/1.46  prop_solver_calls:                      31
% 7.32/1.46  prop_fast_solver_calls:                 480
% 7.32/1.46  smt_solver_calls:                       0
% 7.32/1.46  smt_fast_solver_calls:                  0
% 7.32/1.46  prop_num_of_clauses:                    8207
% 7.32/1.46  prop_preprocess_simplified:             16197
% 7.32/1.47  prop_fo_subsumed:                       0
% 7.32/1.47  prop_solver_time:                       0.
% 7.32/1.47  smt_solver_time:                        0.
% 7.32/1.47  smt_fast_solver_time:                   0.
% 7.32/1.47  prop_fast_solver_time:                  0.
% 7.32/1.47  prop_unsat_core_time:                   0.001
% 7.32/1.47  
% 7.32/1.47  ------ QBF
% 7.32/1.47  
% 7.32/1.47  qbf_q_res:                              0
% 7.32/1.47  qbf_num_tautologies:                    0
% 7.32/1.47  qbf_prep_cycles:                        0
% 7.32/1.47  
% 7.32/1.47  ------ BMC1
% 7.32/1.47  
% 7.32/1.47  bmc1_current_bound:                     -1
% 7.32/1.47  bmc1_last_solved_bound:                 -1
% 7.32/1.47  bmc1_unsat_core_size:                   -1
% 7.32/1.47  bmc1_unsat_core_parents_size:           -1
% 7.32/1.47  bmc1_merge_next_fun:                    0
% 7.32/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.32/1.47  
% 7.32/1.47  ------ Instantiation
% 7.32/1.47  
% 7.32/1.47  inst_num_of_clauses:                    2226
% 7.32/1.47  inst_num_in_passive:                    1148
% 7.32/1.47  inst_num_in_active:                     589
% 7.32/1.47  inst_num_in_unprocessed:                489
% 7.32/1.47  inst_num_of_loops:                      710
% 7.32/1.47  inst_num_of_learning_restarts:          0
% 7.32/1.47  inst_num_moves_active_passive:          119
% 7.32/1.47  inst_lit_activity:                      0
% 7.32/1.47  inst_lit_activity_moves:                1
% 7.32/1.47  inst_num_tautologies:                   0
% 7.32/1.47  inst_num_prop_implied:                  0
% 7.32/1.47  inst_num_existing_simplified:           0
% 7.32/1.47  inst_num_eq_res_simplified:             0
% 7.32/1.47  inst_num_child_elim:                    0
% 7.32/1.47  inst_num_of_dismatching_blockings:      965
% 7.32/1.47  inst_num_of_non_proper_insts:           2227
% 7.32/1.47  inst_num_of_duplicates:                 0
% 7.32/1.47  inst_inst_num_from_inst_to_res:         0
% 7.32/1.47  inst_dismatching_checking_time:         0.
% 7.32/1.47  
% 7.32/1.47  ------ Resolution
% 7.32/1.47  
% 7.32/1.47  res_num_of_clauses:                     0
% 7.32/1.47  res_num_in_passive:                     0
% 7.32/1.47  res_num_in_active:                      0
% 7.32/1.47  res_num_of_loops:                       85
% 7.32/1.47  res_forward_subset_subsumed:            345
% 7.32/1.47  res_backward_subset_subsumed:           0
% 7.32/1.47  res_forward_subsumed:                   0
% 7.32/1.47  res_backward_subsumed:                  0
% 7.32/1.47  res_forward_subsumption_resolution:     0
% 7.32/1.47  res_backward_subsumption_resolution:    0
% 7.32/1.47  res_clause_to_clause_subsumption:       9968
% 7.32/1.47  res_orphan_elimination:                 0
% 7.32/1.47  res_tautology_del:                      77
% 7.32/1.47  res_num_eq_res_simplified:              0
% 7.32/1.47  res_num_sel_changes:                    0
% 7.32/1.47  res_moves_from_active_to_pass:          0
% 7.32/1.47  
% 7.32/1.47  ------ Superposition
% 7.32/1.47  
% 7.32/1.47  sup_time_total:                         0.
% 7.32/1.47  sup_time_generating:                    0.
% 7.32/1.47  sup_time_sim_full:                      0.
% 7.32/1.47  sup_time_sim_immed:                     0.
% 7.32/1.47  
% 7.32/1.47  sup_num_of_clauses:                     950
% 7.32/1.47  sup_num_in_active:                      133
% 7.32/1.47  sup_num_in_passive:                     817
% 7.32/1.47  sup_num_of_loops:                       141
% 7.32/1.47  sup_fw_superposition:                   4268
% 7.32/1.47  sup_bw_superposition:                   2833
% 7.32/1.47  sup_immediate_simplified:               2793
% 7.32/1.47  sup_given_eliminated:                   0
% 7.32/1.47  comparisons_done:                       0
% 7.32/1.47  comparisons_avoided:                    0
% 7.32/1.47  
% 7.32/1.47  ------ Simplifications
% 7.32/1.47  
% 7.32/1.47  
% 7.32/1.47  sim_fw_subset_subsumed:                 49
% 7.32/1.47  sim_bw_subset_subsumed:                 0
% 7.32/1.47  sim_fw_subsumed:                        389
% 7.32/1.47  sim_bw_subsumed:                        1
% 7.32/1.47  sim_fw_subsumption_res:                 0
% 7.32/1.47  sim_bw_subsumption_res:                 0
% 7.32/1.47  sim_tautology_del:                      2
% 7.32/1.47  sim_eq_tautology_del:                   579
% 7.32/1.47  sim_eq_res_simp:                        0
% 7.32/1.47  sim_fw_demodulated:                     895
% 7.32/1.47  sim_bw_demodulated:                     63
% 7.32/1.47  sim_light_normalised:                   2079
% 7.32/1.47  sim_joinable_taut:                      0
% 7.32/1.47  sim_joinable_simp:                      0
% 7.32/1.47  sim_ac_normalised:                      0
% 7.32/1.47  sim_smt_subsumption:                    0
% 7.32/1.47  
%------------------------------------------------------------------------------
