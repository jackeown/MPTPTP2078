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
% DateTime   : Thu Dec  3 11:25:50 EST 2020

% Result     : Theorem 23.39s
% Output     : CNFRefutation 23.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 560 expanded)
%              Number of clauses        :   58 ( 214 expanded)
%              Number of leaves         :   13 ( 143 expanded)
%              Depth                    :   19
%              Number of atoms          :  125 ( 717 expanded)
%              Number of equality atoms :   78 ( 496 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f32,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f30,f24,f24])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f31,f24,f24])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_468,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_467,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1240,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_468,c_467])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8857,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1240,c_0])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_463,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_623,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_463])).

cnf(c_1242,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_623,c_467])).

cnf(c_9,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_466,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_981,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_466])).

cnf(c_1832,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_981])).

cnf(c_4671,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1832])).

cnf(c_4952,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_4671,c_467])).

cnf(c_9331,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_8857,c_4952])).

cnf(c_736,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_468])).

cnf(c_73426,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9331,c_736])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_722,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_470,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3425,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_736,c_470])).

cnf(c_1243,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_736,c_467])).

cnf(c_3472,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3425,c_1243])).

cnf(c_5610,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_722,c_722,c_3472])).

cnf(c_5615,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,X2)))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_5610])).

cnf(c_8804,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1240])).

cnf(c_720,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_9155,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,X1))))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_8804,c_720])).

cnf(c_724,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_9177,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,X1))))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(light_normalisation,[status(thm)],[c_9155,c_724])).

cnf(c_17156,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5615,c_9177])).

cnf(c_17189,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_17156])).

cnf(c_19840,plain,
    ( k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1242,c_17189])).

cnf(c_10,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_465,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20588,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k5_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19840,c_465])).

cnf(c_7573,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1242,c_724])).

cnf(c_17178,plain,
    ( k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7573,c_17156])).

cnf(c_12291,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1243,c_0])).

cnf(c_12518,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_12291])).

cnf(c_17825,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_17178,c_12518])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17990,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17825,c_6])).

cnf(c_19376,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(X0,sK0)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_17990])).

cnf(c_20602,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k1_xboole_0),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19840,c_19376])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_471,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8,c_6])).

cnf(c_20621,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20602,c_471])).

cnf(c_20628,plain,
    ( r1_xboole_0(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20588,c_20621])).

cnf(c_20629,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20628,c_471])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,plain,
    ( r1_xboole_0(sK0,sK2) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73426,c_20629,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.39/3.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.39/3.48  
% 23.39/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.39/3.48  
% 23.39/3.48  ------  iProver source info
% 23.39/3.48  
% 23.39/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.39/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.39/3.48  git: non_committed_changes: false
% 23.39/3.48  git: last_make_outside_of_git: false
% 23.39/3.48  
% 23.39/3.48  ------ 
% 23.39/3.48  
% 23.39/3.48  ------ Input Options
% 23.39/3.48  
% 23.39/3.48  --out_options                           all
% 23.39/3.48  --tptp_safe_out                         true
% 23.39/3.48  --problem_path                          ""
% 23.39/3.48  --include_path                          ""
% 23.39/3.48  --clausifier                            res/vclausify_rel
% 23.39/3.48  --clausifier_options                    ""
% 23.39/3.48  --stdin                                 false
% 23.39/3.48  --stats_out                             all
% 23.39/3.48  
% 23.39/3.48  ------ General Options
% 23.39/3.48  
% 23.39/3.48  --fof                                   false
% 23.39/3.48  --time_out_real                         305.
% 23.39/3.48  --time_out_virtual                      -1.
% 23.39/3.48  --symbol_type_check                     false
% 23.39/3.48  --clausify_out                          false
% 23.39/3.48  --sig_cnt_out                           false
% 23.39/3.48  --trig_cnt_out                          false
% 23.39/3.48  --trig_cnt_out_tolerance                1.
% 23.39/3.48  --trig_cnt_out_sk_spl                   false
% 23.39/3.48  --abstr_cl_out                          false
% 23.39/3.48  
% 23.39/3.48  ------ Global Options
% 23.39/3.48  
% 23.39/3.48  --schedule                              default
% 23.39/3.48  --add_important_lit                     false
% 23.39/3.48  --prop_solver_per_cl                    1000
% 23.39/3.48  --min_unsat_core                        false
% 23.39/3.48  --soft_assumptions                      false
% 23.39/3.48  --soft_lemma_size                       3
% 23.39/3.48  --prop_impl_unit_size                   0
% 23.39/3.48  --prop_impl_unit                        []
% 23.39/3.48  --share_sel_clauses                     true
% 23.39/3.48  --reset_solvers                         false
% 23.39/3.48  --bc_imp_inh                            [conj_cone]
% 23.39/3.48  --conj_cone_tolerance                   3.
% 23.39/3.48  --extra_neg_conj                        none
% 23.39/3.48  --large_theory_mode                     true
% 23.39/3.48  --prolific_symb_bound                   200
% 23.39/3.48  --lt_threshold                          2000
% 23.39/3.48  --clause_weak_htbl                      true
% 23.39/3.48  --gc_record_bc_elim                     false
% 23.39/3.48  
% 23.39/3.48  ------ Preprocessing Options
% 23.39/3.48  
% 23.39/3.48  --preprocessing_flag                    true
% 23.39/3.48  --time_out_prep_mult                    0.1
% 23.39/3.48  --splitting_mode                        input
% 23.39/3.48  --splitting_grd                         true
% 23.39/3.48  --splitting_cvd                         false
% 23.39/3.48  --splitting_cvd_svl                     false
% 23.39/3.48  --splitting_nvd                         32
% 23.39/3.48  --sub_typing                            true
% 23.39/3.48  --prep_gs_sim                           true
% 23.39/3.48  --prep_unflatten                        true
% 23.39/3.48  --prep_res_sim                          true
% 23.39/3.48  --prep_upred                            true
% 23.39/3.48  --prep_sem_filter                       exhaustive
% 23.39/3.48  --prep_sem_filter_out                   false
% 23.39/3.48  --pred_elim                             true
% 23.39/3.48  --res_sim_input                         true
% 23.39/3.48  --eq_ax_congr_red                       true
% 23.39/3.48  --pure_diseq_elim                       true
% 23.39/3.48  --brand_transform                       false
% 23.39/3.48  --non_eq_to_eq                          false
% 23.39/3.48  --prep_def_merge                        true
% 23.39/3.48  --prep_def_merge_prop_impl              false
% 23.39/3.48  --prep_def_merge_mbd                    true
% 23.39/3.48  --prep_def_merge_tr_red                 false
% 23.39/3.48  --prep_def_merge_tr_cl                  false
% 23.39/3.48  --smt_preprocessing                     true
% 23.39/3.48  --smt_ac_axioms                         fast
% 23.39/3.48  --preprocessed_out                      false
% 23.39/3.48  --preprocessed_stats                    false
% 23.39/3.48  
% 23.39/3.48  ------ Abstraction refinement Options
% 23.39/3.48  
% 23.39/3.48  --abstr_ref                             []
% 23.39/3.48  --abstr_ref_prep                        false
% 23.39/3.48  --abstr_ref_until_sat                   false
% 23.39/3.48  --abstr_ref_sig_restrict                funpre
% 23.39/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.39/3.48  --abstr_ref_under                       []
% 23.39/3.48  
% 23.39/3.48  ------ SAT Options
% 23.39/3.48  
% 23.39/3.48  --sat_mode                              false
% 23.39/3.48  --sat_fm_restart_options                ""
% 23.39/3.48  --sat_gr_def                            false
% 23.39/3.48  --sat_epr_types                         true
% 23.39/3.48  --sat_non_cyclic_types                  false
% 23.39/3.48  --sat_finite_models                     false
% 23.39/3.48  --sat_fm_lemmas                         false
% 23.39/3.48  --sat_fm_prep                           false
% 23.39/3.48  --sat_fm_uc_incr                        true
% 23.39/3.48  --sat_out_model                         small
% 23.39/3.48  --sat_out_clauses                       false
% 23.39/3.48  
% 23.39/3.48  ------ QBF Options
% 23.39/3.48  
% 23.39/3.48  --qbf_mode                              false
% 23.39/3.48  --qbf_elim_univ                         false
% 23.39/3.48  --qbf_dom_inst                          none
% 23.39/3.48  --qbf_dom_pre_inst                      false
% 23.39/3.48  --qbf_sk_in                             false
% 23.39/3.48  --qbf_pred_elim                         true
% 23.39/3.48  --qbf_split                             512
% 23.39/3.48  
% 23.39/3.48  ------ BMC1 Options
% 23.39/3.48  
% 23.39/3.48  --bmc1_incremental                      false
% 23.39/3.48  --bmc1_axioms                           reachable_all
% 23.39/3.48  --bmc1_min_bound                        0
% 23.39/3.48  --bmc1_max_bound                        -1
% 23.39/3.48  --bmc1_max_bound_default                -1
% 23.39/3.48  --bmc1_symbol_reachability              true
% 23.39/3.48  --bmc1_property_lemmas                  false
% 23.39/3.48  --bmc1_k_induction                      false
% 23.39/3.48  --bmc1_non_equiv_states                 false
% 23.39/3.48  --bmc1_deadlock                         false
% 23.39/3.48  --bmc1_ucm                              false
% 23.39/3.48  --bmc1_add_unsat_core                   none
% 23.39/3.48  --bmc1_unsat_core_children              false
% 23.39/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.39/3.48  --bmc1_out_stat                         full
% 23.39/3.48  --bmc1_ground_init                      false
% 23.39/3.48  --bmc1_pre_inst_next_state              false
% 23.39/3.48  --bmc1_pre_inst_state                   false
% 23.39/3.48  --bmc1_pre_inst_reach_state             false
% 23.39/3.48  --bmc1_out_unsat_core                   false
% 23.39/3.48  --bmc1_aig_witness_out                  false
% 23.39/3.48  --bmc1_verbose                          false
% 23.39/3.48  --bmc1_dump_clauses_tptp                false
% 23.39/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.39/3.48  --bmc1_dump_file                        -
% 23.39/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.39/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.39/3.48  --bmc1_ucm_extend_mode                  1
% 23.39/3.48  --bmc1_ucm_init_mode                    2
% 23.39/3.48  --bmc1_ucm_cone_mode                    none
% 23.39/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.39/3.48  --bmc1_ucm_relax_model                  4
% 23.39/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.39/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.39/3.48  --bmc1_ucm_layered_model                none
% 23.39/3.48  --bmc1_ucm_max_lemma_size               10
% 23.39/3.48  
% 23.39/3.48  ------ AIG Options
% 23.39/3.48  
% 23.39/3.48  --aig_mode                              false
% 23.39/3.48  
% 23.39/3.48  ------ Instantiation Options
% 23.39/3.48  
% 23.39/3.48  --instantiation_flag                    true
% 23.39/3.48  --inst_sos_flag                         true
% 23.39/3.48  --inst_sos_phase                        true
% 23.39/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.39/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.39/3.48  --inst_lit_sel_side                     num_symb
% 23.39/3.48  --inst_solver_per_active                1400
% 23.39/3.48  --inst_solver_calls_frac                1.
% 23.39/3.48  --inst_passive_queue_type               priority_queues
% 23.39/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.39/3.48  --inst_passive_queues_freq              [25;2]
% 23.39/3.48  --inst_dismatching                      true
% 23.39/3.48  --inst_eager_unprocessed_to_passive     true
% 23.39/3.48  --inst_prop_sim_given                   true
% 23.39/3.48  --inst_prop_sim_new                     false
% 23.39/3.48  --inst_subs_new                         false
% 23.39/3.48  --inst_eq_res_simp                      false
% 23.39/3.48  --inst_subs_given                       false
% 23.39/3.48  --inst_orphan_elimination               true
% 23.39/3.48  --inst_learning_loop_flag               true
% 23.39/3.48  --inst_learning_start                   3000
% 23.39/3.48  --inst_learning_factor                  2
% 23.39/3.48  --inst_start_prop_sim_after_learn       3
% 23.39/3.48  --inst_sel_renew                        solver
% 23.39/3.48  --inst_lit_activity_flag                true
% 23.39/3.48  --inst_restr_to_given                   false
% 23.39/3.48  --inst_activity_threshold               500
% 23.39/3.48  --inst_out_proof                        true
% 23.39/3.48  
% 23.39/3.48  ------ Resolution Options
% 23.39/3.48  
% 23.39/3.48  --resolution_flag                       true
% 23.39/3.48  --res_lit_sel                           adaptive
% 23.39/3.48  --res_lit_sel_side                      none
% 23.39/3.48  --res_ordering                          kbo
% 23.39/3.48  --res_to_prop_solver                    active
% 23.39/3.48  --res_prop_simpl_new                    false
% 23.39/3.48  --res_prop_simpl_given                  true
% 23.39/3.48  --res_passive_queue_type                priority_queues
% 23.39/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.39/3.48  --res_passive_queues_freq               [15;5]
% 23.39/3.48  --res_forward_subs                      full
% 23.39/3.48  --res_backward_subs                     full
% 23.39/3.48  --res_forward_subs_resolution           true
% 23.39/3.48  --res_backward_subs_resolution          true
% 23.39/3.48  --res_orphan_elimination                true
% 23.39/3.48  --res_time_limit                        2.
% 23.39/3.48  --res_out_proof                         true
% 23.39/3.48  
% 23.39/3.48  ------ Superposition Options
% 23.39/3.48  
% 23.39/3.48  --superposition_flag                    true
% 23.39/3.48  --sup_passive_queue_type                priority_queues
% 23.39/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.39/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.39/3.48  --demod_completeness_check              fast
% 23.39/3.48  --demod_use_ground                      true
% 23.39/3.48  --sup_to_prop_solver                    passive
% 23.39/3.48  --sup_prop_simpl_new                    true
% 23.39/3.48  --sup_prop_simpl_given                  true
% 23.39/3.48  --sup_fun_splitting                     true
% 23.39/3.48  --sup_smt_interval                      50000
% 23.39/3.48  
% 23.39/3.48  ------ Superposition Simplification Setup
% 23.39/3.48  
% 23.39/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.39/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.39/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.39/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.39/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.39/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.39/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.39/3.48  --sup_immed_triv                        [TrivRules]
% 23.39/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.39/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.39/3.48  --sup_immed_bw_main                     []
% 23.39/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.39/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.39/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.39/3.48  --sup_input_bw                          []
% 23.39/3.48  
% 23.39/3.48  ------ Combination Options
% 23.39/3.48  
% 23.39/3.48  --comb_res_mult                         3
% 23.39/3.48  --comb_sup_mult                         2
% 23.39/3.48  --comb_inst_mult                        10
% 23.39/3.48  
% 23.39/3.48  ------ Debug Options
% 23.39/3.48  
% 23.39/3.48  --dbg_backtrace                         false
% 23.39/3.48  --dbg_dump_prop_clauses                 false
% 23.39/3.48  --dbg_dump_prop_clauses_file            -
% 23.39/3.48  --dbg_out_stat                          false
% 23.39/3.48  ------ Parsing...
% 23.39/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.39/3.48  
% 23.39/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.39/3.48  
% 23.39/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.39/3.48  
% 23.39/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.39/3.48  ------ Proving...
% 23.39/3.48  ------ Problem Properties 
% 23.39/3.48  
% 23.39/3.48  
% 23.39/3.48  clauses                                 13
% 23.39/3.48  conjectures                             2
% 23.39/3.48  EPR                                     1
% 23.39/3.48  Horn                                    13
% 23.39/3.48  unary                                   9
% 23.39/3.48  binary                                  4
% 23.39/3.48  lits                                    17
% 23.39/3.48  lits eq                                 8
% 23.39/3.48  fd_pure                                 0
% 23.39/3.48  fd_pseudo                               0
% 23.39/3.48  fd_cond                                 0
% 23.39/3.48  fd_pseudo_cond                          0
% 23.39/3.48  AC symbols                              0
% 23.39/3.48  
% 23.39/3.48  ------ Schedule dynamic 5 is on 
% 23.39/3.48  
% 23.39/3.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.39/3.48  
% 23.39/3.48  
% 23.39/3.48  ------ 
% 23.39/3.48  Current options:
% 23.39/3.48  ------ 
% 23.39/3.48  
% 23.39/3.48  ------ Input Options
% 23.39/3.48  
% 23.39/3.48  --out_options                           all
% 23.39/3.48  --tptp_safe_out                         true
% 23.39/3.48  --problem_path                          ""
% 23.39/3.48  --include_path                          ""
% 23.39/3.48  --clausifier                            res/vclausify_rel
% 23.39/3.48  --clausifier_options                    ""
% 23.39/3.48  --stdin                                 false
% 23.39/3.48  --stats_out                             all
% 23.39/3.48  
% 23.39/3.48  ------ General Options
% 23.39/3.48  
% 23.39/3.48  --fof                                   false
% 23.39/3.48  --time_out_real                         305.
% 23.39/3.48  --time_out_virtual                      -1.
% 23.39/3.48  --symbol_type_check                     false
% 23.39/3.48  --clausify_out                          false
% 23.39/3.48  --sig_cnt_out                           false
% 23.39/3.48  --trig_cnt_out                          false
% 23.39/3.48  --trig_cnt_out_tolerance                1.
% 23.39/3.48  --trig_cnt_out_sk_spl                   false
% 23.39/3.48  --abstr_cl_out                          false
% 23.39/3.48  
% 23.39/3.48  ------ Global Options
% 23.39/3.48  
% 23.39/3.48  --schedule                              default
% 23.39/3.48  --add_important_lit                     false
% 23.39/3.48  --prop_solver_per_cl                    1000
% 23.39/3.48  --min_unsat_core                        false
% 23.39/3.48  --soft_assumptions                      false
% 23.39/3.48  --soft_lemma_size                       3
% 23.39/3.48  --prop_impl_unit_size                   0
% 23.39/3.48  --prop_impl_unit                        []
% 23.39/3.48  --share_sel_clauses                     true
% 23.39/3.48  --reset_solvers                         false
% 23.39/3.48  --bc_imp_inh                            [conj_cone]
% 23.39/3.48  --conj_cone_tolerance                   3.
% 23.39/3.48  --extra_neg_conj                        none
% 23.39/3.48  --large_theory_mode                     true
% 23.39/3.48  --prolific_symb_bound                   200
% 23.39/3.48  --lt_threshold                          2000
% 23.39/3.48  --clause_weak_htbl                      true
% 23.39/3.48  --gc_record_bc_elim                     false
% 23.39/3.48  
% 23.39/3.48  ------ Preprocessing Options
% 23.39/3.48  
% 23.39/3.48  --preprocessing_flag                    true
% 23.39/3.48  --time_out_prep_mult                    0.1
% 23.39/3.48  --splitting_mode                        input
% 23.39/3.48  --splitting_grd                         true
% 23.39/3.48  --splitting_cvd                         false
% 23.39/3.48  --splitting_cvd_svl                     false
% 23.39/3.48  --splitting_nvd                         32
% 23.39/3.48  --sub_typing                            true
% 23.39/3.48  --prep_gs_sim                           true
% 23.39/3.48  --prep_unflatten                        true
% 23.39/3.48  --prep_res_sim                          true
% 23.39/3.48  --prep_upred                            true
% 23.39/3.48  --prep_sem_filter                       exhaustive
% 23.39/3.48  --prep_sem_filter_out                   false
% 23.39/3.48  --pred_elim                             true
% 23.39/3.48  --res_sim_input                         true
% 23.39/3.48  --eq_ax_congr_red                       true
% 23.39/3.48  --pure_diseq_elim                       true
% 23.39/3.48  --brand_transform                       false
% 23.39/3.48  --non_eq_to_eq                          false
% 23.39/3.48  --prep_def_merge                        true
% 23.39/3.48  --prep_def_merge_prop_impl              false
% 23.39/3.48  --prep_def_merge_mbd                    true
% 23.39/3.48  --prep_def_merge_tr_red                 false
% 23.39/3.48  --prep_def_merge_tr_cl                  false
% 23.39/3.48  --smt_preprocessing                     true
% 23.39/3.48  --smt_ac_axioms                         fast
% 23.39/3.48  --preprocessed_out                      false
% 23.39/3.48  --preprocessed_stats                    false
% 23.39/3.48  
% 23.39/3.48  ------ Abstraction refinement Options
% 23.39/3.48  
% 23.39/3.48  --abstr_ref                             []
% 23.39/3.48  --abstr_ref_prep                        false
% 23.39/3.48  --abstr_ref_until_sat                   false
% 23.39/3.48  --abstr_ref_sig_restrict                funpre
% 23.39/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.39/3.48  --abstr_ref_under                       []
% 23.39/3.48  
% 23.39/3.48  ------ SAT Options
% 23.39/3.48  
% 23.39/3.48  --sat_mode                              false
% 23.39/3.48  --sat_fm_restart_options                ""
% 23.39/3.48  --sat_gr_def                            false
% 23.39/3.48  --sat_epr_types                         true
% 23.39/3.48  --sat_non_cyclic_types                  false
% 23.39/3.48  --sat_finite_models                     false
% 23.39/3.48  --sat_fm_lemmas                         false
% 23.39/3.48  --sat_fm_prep                           false
% 23.39/3.48  --sat_fm_uc_incr                        true
% 23.39/3.48  --sat_out_model                         small
% 23.39/3.48  --sat_out_clauses                       false
% 23.39/3.48  
% 23.39/3.48  ------ QBF Options
% 23.39/3.48  
% 23.39/3.48  --qbf_mode                              false
% 23.39/3.48  --qbf_elim_univ                         false
% 23.39/3.48  --qbf_dom_inst                          none
% 23.39/3.48  --qbf_dom_pre_inst                      false
% 23.39/3.48  --qbf_sk_in                             false
% 23.39/3.48  --qbf_pred_elim                         true
% 23.39/3.48  --qbf_split                             512
% 23.39/3.48  
% 23.39/3.48  ------ BMC1 Options
% 23.39/3.48  
% 23.39/3.48  --bmc1_incremental                      false
% 23.39/3.48  --bmc1_axioms                           reachable_all
% 23.39/3.48  --bmc1_min_bound                        0
% 23.39/3.48  --bmc1_max_bound                        -1
% 23.39/3.48  --bmc1_max_bound_default                -1
% 23.39/3.48  --bmc1_symbol_reachability              true
% 23.39/3.48  --bmc1_property_lemmas                  false
% 23.39/3.48  --bmc1_k_induction                      false
% 23.39/3.48  --bmc1_non_equiv_states                 false
% 23.39/3.48  --bmc1_deadlock                         false
% 23.39/3.48  --bmc1_ucm                              false
% 23.39/3.48  --bmc1_add_unsat_core                   none
% 23.39/3.48  --bmc1_unsat_core_children              false
% 23.39/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.39/3.48  --bmc1_out_stat                         full
% 23.39/3.48  --bmc1_ground_init                      false
% 23.39/3.48  --bmc1_pre_inst_next_state              false
% 23.39/3.48  --bmc1_pre_inst_state                   false
% 23.39/3.48  --bmc1_pre_inst_reach_state             false
% 23.39/3.48  --bmc1_out_unsat_core                   false
% 23.39/3.48  --bmc1_aig_witness_out                  false
% 23.39/3.48  --bmc1_verbose                          false
% 23.39/3.48  --bmc1_dump_clauses_tptp                false
% 23.39/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.39/3.48  --bmc1_dump_file                        -
% 23.39/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.39/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.39/3.48  --bmc1_ucm_extend_mode                  1
% 23.39/3.48  --bmc1_ucm_init_mode                    2
% 23.39/3.48  --bmc1_ucm_cone_mode                    none
% 23.39/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.39/3.48  --bmc1_ucm_relax_model                  4
% 23.39/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.39/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.39/3.48  --bmc1_ucm_layered_model                none
% 23.39/3.48  --bmc1_ucm_max_lemma_size               10
% 23.39/3.48  
% 23.39/3.48  ------ AIG Options
% 23.39/3.48  
% 23.39/3.48  --aig_mode                              false
% 23.39/3.48  
% 23.39/3.48  ------ Instantiation Options
% 23.39/3.48  
% 23.39/3.48  --instantiation_flag                    true
% 23.39/3.48  --inst_sos_flag                         true
% 23.39/3.48  --inst_sos_phase                        true
% 23.39/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.39/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.39/3.48  --inst_lit_sel_side                     none
% 23.39/3.48  --inst_solver_per_active                1400
% 23.39/3.48  --inst_solver_calls_frac                1.
% 23.39/3.48  --inst_passive_queue_type               priority_queues
% 23.39/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.39/3.48  --inst_passive_queues_freq              [25;2]
% 23.39/3.48  --inst_dismatching                      true
% 23.39/3.48  --inst_eager_unprocessed_to_passive     true
% 23.39/3.48  --inst_prop_sim_given                   true
% 23.39/3.48  --inst_prop_sim_new                     false
% 23.39/3.48  --inst_subs_new                         false
% 23.39/3.48  --inst_eq_res_simp                      false
% 23.39/3.48  --inst_subs_given                       false
% 23.39/3.48  --inst_orphan_elimination               true
% 23.39/3.48  --inst_learning_loop_flag               true
% 23.39/3.48  --inst_learning_start                   3000
% 23.39/3.48  --inst_learning_factor                  2
% 23.39/3.48  --inst_start_prop_sim_after_learn       3
% 23.39/3.48  --inst_sel_renew                        solver
% 23.39/3.48  --inst_lit_activity_flag                true
% 23.39/3.48  --inst_restr_to_given                   false
% 23.39/3.48  --inst_activity_threshold               500
% 23.39/3.48  --inst_out_proof                        true
% 23.39/3.48  
% 23.39/3.48  ------ Resolution Options
% 23.39/3.48  
% 23.39/3.48  --resolution_flag                       false
% 23.39/3.48  --res_lit_sel                           adaptive
% 23.39/3.48  --res_lit_sel_side                      none
% 23.39/3.48  --res_ordering                          kbo
% 23.39/3.48  --res_to_prop_solver                    active
% 23.39/3.48  --res_prop_simpl_new                    false
% 23.39/3.48  --res_prop_simpl_given                  true
% 23.39/3.48  --res_passive_queue_type                priority_queues
% 23.39/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.39/3.48  --res_passive_queues_freq               [15;5]
% 23.39/3.48  --res_forward_subs                      full
% 23.39/3.48  --res_backward_subs                     full
% 23.39/3.48  --res_forward_subs_resolution           true
% 23.39/3.48  --res_backward_subs_resolution          true
% 23.39/3.48  --res_orphan_elimination                true
% 23.39/3.48  --res_time_limit                        2.
% 23.39/3.48  --res_out_proof                         true
% 23.39/3.48  
% 23.39/3.48  ------ Superposition Options
% 23.39/3.48  
% 23.39/3.48  --superposition_flag                    true
% 23.39/3.48  --sup_passive_queue_type                priority_queues
% 23.39/3.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.39/3.48  --sup_passive_queues_freq               [8;1;4]
% 23.39/3.48  --demod_completeness_check              fast
% 23.39/3.48  --demod_use_ground                      true
% 23.39/3.48  --sup_to_prop_solver                    passive
% 23.39/3.48  --sup_prop_simpl_new                    true
% 23.39/3.48  --sup_prop_simpl_given                  true
% 23.39/3.48  --sup_fun_splitting                     true
% 23.39/3.48  --sup_smt_interval                      50000
% 23.39/3.48  
% 23.39/3.48  ------ Superposition Simplification Setup
% 23.39/3.48  
% 23.39/3.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.39/3.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.39/3.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.39/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.39/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.39/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.39/3.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.39/3.48  --sup_immed_triv                        [TrivRules]
% 23.39/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.39/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.39/3.48  --sup_immed_bw_main                     []
% 23.39/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.39/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.39/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.39/3.48  --sup_input_bw                          []
% 23.39/3.48  
% 23.39/3.48  ------ Combination Options
% 23.39/3.48  
% 23.39/3.48  --comb_res_mult                         3
% 23.39/3.48  --comb_sup_mult                         2
% 23.39/3.48  --comb_inst_mult                        10
% 23.39/3.48  
% 23.39/3.48  ------ Debug Options
% 23.39/3.48  
% 23.39/3.48  --dbg_backtrace                         false
% 23.39/3.48  --dbg_dump_prop_clauses                 false
% 23.39/3.48  --dbg_dump_prop_clauses_file            -
% 23.39/3.48  --dbg_out_stat                          false
% 23.39/3.48  
% 23.39/3.48  
% 23.39/3.48  
% 23.39/3.48  
% 23.39/3.48  ------ Proving...
% 23.39/3.48  
% 23.39/3.48  
% 23.39/3.48  % SZS status Theorem for theBenchmark.p
% 23.39/3.48  
% 23.39/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.39/3.48  
% 23.39/3.48  fof(f5,axiom,(
% 23.39/3.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f25,plain,(
% 23.39/3.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.39/3.48    inference(cnf_transformation,[],[f5])).
% 23.39/3.48  
% 23.39/3.48  fof(f6,axiom,(
% 23.39/3.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f15,plain,(
% 23.39/3.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.39/3.48    inference(ennf_transformation,[],[f6])).
% 23.39/3.48  
% 23.39/3.48  fof(f26,plain,(
% 23.39/3.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.39/3.48    inference(cnf_transformation,[],[f15])).
% 23.39/3.48  
% 23.39/3.48  fof(f1,axiom,(
% 23.39/3.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f20,plain,(
% 23.39/3.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.39/3.48    inference(cnf_transformation,[],[f1])).
% 23.39/3.48  
% 23.39/3.48  fof(f12,conjecture,(
% 23.39/3.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f13,negated_conjecture,(
% 23.39/3.48    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 23.39/3.48    inference(negated_conjecture,[],[f12])).
% 23.39/3.48  
% 23.39/3.48  fof(f16,plain,(
% 23.39/3.48    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 23.39/3.48    inference(ennf_transformation,[],[f13])).
% 23.39/3.48  
% 23.39/3.48  fof(f18,plain,(
% 23.39/3.48    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 23.39/3.48    introduced(choice_axiom,[])).
% 23.39/3.48  
% 23.39/3.48  fof(f19,plain,(
% 23.39/3.48    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 23.39/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 23.39/3.48  
% 23.39/3.48  fof(f32,plain,(
% 23.39/3.48    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 23.39/3.48    inference(cnf_transformation,[],[f19])).
% 23.39/3.48  
% 23.39/3.48  fof(f4,axiom,(
% 23.39/3.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f24,plain,(
% 23.39/3.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.39/3.48    inference(cnf_transformation,[],[f4])).
% 23.39/3.48  
% 23.39/3.48  fof(f40,plain,(
% 23.39/3.48    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 23.39/3.48    inference(definition_unfolding,[],[f32,f24])).
% 23.39/3.48  
% 23.39/3.48  fof(f10,axiom,(
% 23.39/3.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f30,plain,(
% 23.39/3.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 23.39/3.48    inference(cnf_transformation,[],[f10])).
% 23.39/3.48  
% 23.39/3.48  fof(f38,plain,(
% 23.39/3.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 23.39/3.48    inference(definition_unfolding,[],[f30,f24,f24])).
% 23.39/3.48  
% 23.39/3.48  fof(f8,axiom,(
% 23.39/3.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f28,plain,(
% 23.39/3.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.39/3.48    inference(cnf_transformation,[],[f8])).
% 23.39/3.48  
% 23.39/3.48  fof(f36,plain,(
% 23.39/3.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 23.39/3.48    inference(definition_unfolding,[],[f28,f24])).
% 23.39/3.48  
% 23.39/3.48  fof(f2,axiom,(
% 23.39/3.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f14,plain,(
% 23.39/3.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 23.39/3.48    inference(rectify,[],[f2])).
% 23.39/3.48  
% 23.39/3.48  fof(f21,plain,(
% 23.39/3.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 23.39/3.48    inference(cnf_transformation,[],[f14])).
% 23.39/3.48  
% 23.39/3.48  fof(f3,axiom,(
% 23.39/3.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f17,plain,(
% 23.39/3.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 23.39/3.48    inference(nnf_transformation,[],[f3])).
% 23.39/3.48  
% 23.39/3.48  fof(f23,plain,(
% 23.39/3.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 23.39/3.48    inference(cnf_transformation,[],[f17])).
% 23.39/3.48  
% 23.39/3.48  fof(f34,plain,(
% 23.39/3.48    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 23.39/3.48    inference(definition_unfolding,[],[f23,f24])).
% 23.39/3.48  
% 23.39/3.48  fof(f11,axiom,(
% 23.39/3.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f31,plain,(
% 23.39/3.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 23.39/3.48    inference(cnf_transformation,[],[f11])).
% 23.39/3.48  
% 23.39/3.48  fof(f39,plain,(
% 23.39/3.48    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 23.39/3.48    inference(definition_unfolding,[],[f31,f24,f24])).
% 23.39/3.48  
% 23.39/3.48  fof(f7,axiom,(
% 23.39/3.48    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f27,plain,(
% 23.39/3.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 23.39/3.48    inference(cnf_transformation,[],[f7])).
% 23.39/3.48  
% 23.39/3.48  fof(f9,axiom,(
% 23.39/3.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.39/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.39/3.48  
% 23.39/3.48  fof(f29,plain,(
% 23.39/3.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.39/3.48    inference(cnf_transformation,[],[f9])).
% 23.39/3.48  
% 23.39/3.48  fof(f37,plain,(
% 23.39/3.48    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 23.39/3.48    inference(definition_unfolding,[],[f29,f24])).
% 23.39/3.48  
% 23.39/3.48  fof(f33,plain,(
% 23.39/3.48    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 23.39/3.48    inference(cnf_transformation,[],[f19])).
% 23.39/3.48  
% 23.39/3.48  cnf(c_4,plain,
% 23.39/3.48      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 23.39/3.48      inference(cnf_transformation,[],[f25]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_468,plain,
% 23.39/3.48      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 23.39/3.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_5,plain,
% 23.39/3.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.39/3.48      inference(cnf_transformation,[],[f26]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_467,plain,
% 23.39/3.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.39/3.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_1240,plain,
% 23.39/3.48      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_468,c_467]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_0,plain,
% 23.39/3.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.39/3.48      inference(cnf_transformation,[],[f20]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_8857,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_1240,c_0]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_12,negated_conjecture,
% 23.39/3.48      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 23.39/3.48      inference(cnf_transformation,[],[f40]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_463,plain,
% 23.39/3.48      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 23.39/3.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_623,plain,
% 23.39/3.48      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
% 23.39/3.48      inference(demodulation,[status(thm)],[c_0,c_463]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_1242,plain,
% 23.39/3.48      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_623,c_467]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_9,plain,
% 23.39/3.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 23.39/3.48      inference(cnf_transformation,[],[f38]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_7,plain,
% 23.39/3.48      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 23.39/3.48      inference(cnf_transformation,[],[f36]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_466,plain,
% 23.39/3.48      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 23.39/3.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_981,plain,
% 23.39/3.48      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_9,c_466]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_1832,plain,
% 23.39/3.48      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_0,c_981]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_4671,plain,
% 23.39/3.48      ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_1242,c_1832]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_4952,plain,
% 23.39/3.48      ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_4671,c_467]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_9331,plain,
% 23.39/3.48      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_8857,c_4952]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_736,plain,
% 23.39/3.48      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_0,c_468]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_73426,plain,
% 23.39/3.48      ( r1_tarski(sK0,sK1) = iProver_top ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_9331,c_736]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_1,plain,
% 23.39/3.48      ( k3_xboole_0(X0,X0) = X0 ),
% 23.39/3.48      inference(cnf_transformation,[],[f21]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_722,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_2,plain,
% 23.39/3.48      ( ~ r1_tarski(X0,X1)
% 23.39/3.48      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.39/3.48      inference(cnf_transformation,[],[f34]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_470,plain,
% 23.39/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 23.39/3.48      | r1_tarski(X0,X1) != iProver_top ),
% 23.39/3.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_3425,plain,
% 23.39/3.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_736,c_470]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_1243,plain,
% 23.39/3.48      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_736,c_467]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_3472,plain,
% 23.39/3.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 23.39/3.48      inference(light_normalisation,[status(thm)],[c_3425,c_1243]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_5610,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 23.39/3.48      inference(light_normalisation,[status(thm)],[c_722,c_722,c_3472]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_5615,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X0,k3_xboole_0(X1,X2)))))) = k1_xboole_0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_9,c_5610]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_8804,plain,
% 23.39/3.48      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_0,c_1240]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_720,plain,
% 23.39/3.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_9155,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,X1))))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_8804,c_720]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_724,plain,
% 23.39/3.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_9177,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X0,X1))))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 23.39/3.48      inference(light_normalisation,[status(thm)],[c_9155,c_724]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_17156,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0)))) = k1_xboole_0 ),
% 23.39/3.48      inference(demodulation,[status(thm)],[c_5615,c_9177]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_17189,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,X2)))) = k1_xboole_0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_0,c_17156]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_19840,plain,
% 23.39/3.48      ( k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_1242,c_17189]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_10,plain,
% 23.39/3.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 23.39/3.48      inference(cnf_transformation,[],[f39]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_465,plain,
% 23.39/3.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = iProver_top ),
% 23.39/3.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_20588,plain,
% 23.39/3.48      ( r1_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k5_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_19840,c_465]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_7573,plain,
% 23.39/3.48      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_1242,c_724]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_17178,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k1_xboole_0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_7573,c_17156]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_12291,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_1243,c_0]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_12518,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_0,c_12291]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_17825,plain,
% 23.39/3.48      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_17178,c_12518]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_6,plain,
% 23.39/3.48      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.39/3.48      inference(cnf_transformation,[],[f27]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_17990,plain,
% 23.39/3.48      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),X0) = k1_xboole_0 ),
% 23.39/3.48      inference(light_normalisation,[status(thm)],[c_17825,c_6]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_19376,plain,
% 23.39/3.48      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(X0,sK0)),X0) = k1_xboole_0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_0,c_17990]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_20602,plain,
% 23.39/3.48      ( k3_xboole_0(k5_xboole_0(sK0,k1_xboole_0),sK2) = k1_xboole_0 ),
% 23.39/3.48      inference(superposition,[status(thm)],[c_19840,c_19376]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_8,plain,
% 23.39/3.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 23.39/3.48      inference(cnf_transformation,[],[f37]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_471,plain,
% 23.39/3.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.39/3.48      inference(light_normalisation,[status(thm)],[c_8,c_6]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_20621,plain,
% 23.39/3.48      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 23.39/3.48      inference(demodulation,[status(thm)],[c_20602,c_471]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_20628,plain,
% 23.39/3.48      ( r1_xboole_0(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK2,k1_xboole_0)) = iProver_top ),
% 23.39/3.48      inference(demodulation,[status(thm)],[c_20588,c_20621]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_20629,plain,
% 23.39/3.48      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 23.39/3.48      inference(demodulation,[status(thm)],[c_20628,c_471]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_11,negated_conjecture,
% 23.39/3.48      ( ~ r1_xboole_0(sK0,sK2) | ~ r1_tarski(sK0,sK1) ),
% 23.39/3.48      inference(cnf_transformation,[],[f33]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(c_14,plain,
% 23.39/3.48      ( r1_xboole_0(sK0,sK2) != iProver_top
% 23.39/3.48      | r1_tarski(sK0,sK1) != iProver_top ),
% 23.39/3.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.39/3.48  
% 23.39/3.48  cnf(contradiction,plain,
% 23.39/3.48      ( $false ),
% 23.39/3.48      inference(minisat,[status(thm)],[c_73426,c_20629,c_14]) ).
% 23.39/3.48  
% 23.39/3.48  
% 23.39/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.39/3.48  
% 23.39/3.48  ------                               Statistics
% 23.39/3.48  
% 23.39/3.48  ------ General
% 23.39/3.48  
% 23.39/3.48  abstr_ref_over_cycles:                  0
% 23.39/3.48  abstr_ref_under_cycles:                 0
% 23.39/3.48  gc_basic_clause_elim:                   0
% 23.39/3.48  forced_gc_time:                         0
% 23.39/3.48  parsing_time:                           0.015
% 23.39/3.48  unif_index_cands_time:                  0.
% 23.39/3.48  unif_index_add_time:                    0.
% 23.39/3.48  orderings_time:                         0.
% 23.39/3.48  out_proof_time:                         0.01
% 23.39/3.48  total_time:                             2.64
% 23.39/3.48  num_of_symbols:                         39
% 23.39/3.48  num_of_terms:                           101217
% 23.39/3.48  
% 23.39/3.48  ------ Preprocessing
% 23.39/3.48  
% 23.39/3.48  num_of_splits:                          0
% 23.39/3.48  num_of_split_atoms:                     0
% 23.39/3.48  num_of_reused_defs:                     0
% 23.39/3.48  num_eq_ax_congr_red:                    0
% 23.39/3.48  num_of_sem_filtered_clauses:            1
% 23.39/3.48  num_of_subtypes:                        0
% 23.39/3.48  monotx_restored_types:                  0
% 23.39/3.48  sat_num_of_epr_types:                   0
% 23.39/3.48  sat_num_of_non_cyclic_types:            0
% 23.39/3.48  sat_guarded_non_collapsed_types:        0
% 23.39/3.48  num_pure_diseq_elim:                    0
% 23.39/3.48  simp_replaced_by:                       0
% 23.39/3.48  res_preprocessed:                       52
% 23.39/3.48  prep_upred:                             0
% 23.39/3.48  prep_unflattend:                        16
% 23.39/3.48  smt_new_axioms:                         0
% 23.39/3.48  pred_elim_cands:                        2
% 23.39/3.48  pred_elim:                              0
% 23.39/3.48  pred_elim_cl:                           0
% 23.39/3.48  pred_elim_cycles:                       2
% 23.39/3.48  merged_defs:                            6
% 23.39/3.48  merged_defs_ncl:                        0
% 23.39/3.48  bin_hyper_res:                          6
% 23.39/3.48  prep_cycles:                            3
% 23.39/3.48  pred_elim_time:                         0.002
% 23.39/3.48  splitting_time:                         0.
% 23.39/3.48  sem_filter_time:                        0.
% 23.39/3.48  monotx_time:                            0.001
% 23.39/3.48  subtype_inf_time:                       0.
% 23.39/3.48  
% 23.39/3.48  ------ Problem properties
% 23.39/3.48  
% 23.39/3.48  clauses:                                13
% 23.39/3.48  conjectures:                            2
% 23.39/3.48  epr:                                    1
% 23.39/3.48  horn:                                   13
% 23.39/3.48  ground:                                 2
% 23.39/3.48  unary:                                  9
% 23.39/3.48  binary:                                 4
% 23.39/3.48  lits:                                   17
% 23.39/3.48  lits_eq:                                8
% 23.39/3.48  fd_pure:                                0
% 23.39/3.48  fd_pseudo:                              0
% 23.39/3.48  fd_cond:                                0
% 23.39/3.48  fd_pseudo_cond:                         0
% 23.39/3.48  ac_symbols:                             0
% 23.39/3.48  
% 23.39/3.48  ------ Propositional Solver
% 23.39/3.48  
% 23.39/3.48  prop_solver_calls:                      34
% 23.39/3.48  prop_fast_solver_calls:                 660
% 23.39/3.48  smt_solver_calls:                       0
% 23.39/3.48  smt_fast_solver_calls:                  0
% 23.39/3.48  prop_num_of_clauses:                    22913
% 23.39/3.48  prop_preprocess_simplified:             21262
% 23.39/3.48  prop_fo_subsumed:                       0
% 23.39/3.48  prop_solver_time:                       0.
% 23.39/3.48  smt_solver_time:                        0.
% 23.39/3.48  smt_fast_solver_time:                   0.
% 23.39/3.48  prop_fast_solver_time:                  0.
% 23.39/3.48  prop_unsat_core_time:                   0.002
% 23.39/3.48  
% 23.39/3.48  ------ QBF
% 23.39/3.48  
% 23.39/3.48  qbf_q_res:                              0
% 23.39/3.48  qbf_num_tautologies:                    0
% 23.39/3.48  qbf_prep_cycles:                        0
% 23.39/3.48  
% 23.39/3.48  ------ BMC1
% 23.39/3.48  
% 23.39/3.48  bmc1_current_bound:                     -1
% 23.39/3.48  bmc1_last_solved_bound:                 -1
% 23.39/3.48  bmc1_unsat_core_size:                   -1
% 23.39/3.48  bmc1_unsat_core_parents_size:           -1
% 23.39/3.48  bmc1_merge_next_fun:                    0
% 23.39/3.48  bmc1_unsat_core_clauses_time:           0.
% 23.39/3.48  
% 23.39/3.48  ------ Instantiation
% 23.39/3.48  
% 23.39/3.48  inst_num_of_clauses:                    3721
% 23.39/3.48  inst_num_in_passive:                    1322
% 23.39/3.48  inst_num_in_active:                     1411
% 23.39/3.48  inst_num_in_unprocessed:                988
% 23.39/3.48  inst_num_of_loops:                      1570
% 23.39/3.48  inst_num_of_learning_restarts:          0
% 23.39/3.48  inst_num_moves_active_passive:          151
% 23.39/3.48  inst_lit_activity:                      0
% 23.39/3.48  inst_lit_activity_moves:                0
% 23.39/3.48  inst_num_tautologies:                   0
% 23.39/3.48  inst_num_prop_implied:                  0
% 23.39/3.48  inst_num_existing_simplified:           0
% 23.39/3.48  inst_num_eq_res_simplified:             0
% 23.39/3.48  inst_num_child_elim:                    0
% 23.39/3.48  inst_num_of_dismatching_blockings:      1727
% 23.39/3.48  inst_num_of_non_proper_insts:           4902
% 23.39/3.48  inst_num_of_duplicates:                 0
% 23.39/3.48  inst_inst_num_from_inst_to_res:         0
% 23.39/3.48  inst_dismatching_checking_time:         0.
% 23.39/3.48  
% 23.39/3.48  ------ Resolution
% 23.39/3.48  
% 23.39/3.48  res_num_of_clauses:                     0
% 23.39/3.48  res_num_in_passive:                     0
% 23.39/3.48  res_num_in_active:                      0
% 23.39/3.48  res_num_of_loops:                       55
% 23.39/3.48  res_forward_subset_subsumed:            699
% 23.39/3.48  res_backward_subset_subsumed:           0
% 23.39/3.48  res_forward_subsumed:                   0
% 23.39/3.48  res_backward_subsumed:                  0
% 23.39/3.48  res_forward_subsumption_resolution:     0
% 23.39/3.48  res_backward_subsumption_resolution:    0
% 23.39/3.48  res_clause_to_clause_subsumption:       79634
% 23.39/3.48  res_orphan_elimination:                 0
% 23.39/3.48  res_tautology_del:                      439
% 23.39/3.48  res_num_eq_res_simplified:              0
% 23.39/3.48  res_num_sel_changes:                    0
% 23.39/3.48  res_moves_from_active_to_pass:          0
% 23.39/3.48  
% 23.39/3.48  ------ Superposition
% 23.39/3.48  
% 23.39/3.48  sup_time_total:                         0.
% 23.39/3.48  sup_time_generating:                    0.
% 23.39/3.48  sup_time_sim_full:                      0.
% 23.39/3.48  sup_time_sim_immed:                     0.
% 23.39/3.48  
% 23.39/3.48  sup_num_of_clauses:                     5153
% 23.39/3.48  sup_num_in_active:                      203
% 23.39/3.48  sup_num_in_passive:                     4950
% 23.39/3.48  sup_num_of_loops:                       312
% 23.39/3.48  sup_fw_superposition:                   13345
% 23.39/3.48  sup_bw_superposition:                   12628
% 23.39/3.48  sup_immediate_simplified:               13331
% 23.39/3.48  sup_given_eliminated:                   17
% 23.39/3.48  comparisons_done:                       0
% 23.39/3.48  comparisons_avoided:                    0
% 23.39/3.48  
% 23.39/3.48  ------ Simplifications
% 23.39/3.48  
% 23.39/3.48  
% 23.39/3.48  sim_fw_subset_subsumed:                 40
% 23.39/3.48  sim_bw_subset_subsumed:                 0
% 23.39/3.48  sim_fw_subsumed:                        2276
% 23.39/3.48  sim_bw_subsumed:                        190
% 23.39/3.48  sim_fw_subsumption_res:                 0
% 23.39/3.48  sim_bw_subsumption_res:                 0
% 23.39/3.48  sim_tautology_del:                      0
% 23.39/3.48  sim_eq_tautology_del:                   3139
% 23.39/3.48  sim_eq_res_simp:                        14
% 23.39/3.48  sim_fw_demodulated:                     10508
% 23.39/3.48  sim_bw_demodulated:                     1028
% 23.39/3.48  sim_light_normalised:                   5615
% 23.39/3.48  sim_joinable_taut:                      0
% 23.39/3.48  sim_joinable_simp:                      0
% 23.39/3.48  sim_ac_normalised:                      0
% 23.39/3.48  sim_smt_subsumption:                    0
% 23.39/3.48  
%------------------------------------------------------------------------------
