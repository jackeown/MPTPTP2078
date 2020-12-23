%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:33 EST 2020

% Result     : Theorem 11.66s
% Output     : CNFRefutation 11.66s
% Verified   : 
% Statistics : Number of formulae       :  119 (14738 expanded)
%              Number of clauses        :   84 (4911 expanded)
%              Number of leaves         :   13 (4253 expanded)
%              Depth                    :   35
%              Number of atoms          :  127 (14956 expanded)
%              Number of equality atoms :  117 (14676 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f33,f23])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f23,f23])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f31,f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f13,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).

fof(f34,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f34,f23,f35])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_145,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_4,c_3,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_636,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_145,c_5])).

cnf(c_644,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_636,c_145])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_436,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_11])).

cnf(c_628,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_436,c_145])).

cnf(c_824,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_644,c_628])).

cnf(c_826,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_824,c_7])).

cnf(c_325,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1460,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_826,c_325])).

cnf(c_10,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_315,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_658,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_315,c_5])).

cnf(c_664,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_658])).

cnf(c_1748,plain,
    ( r1_xboole_0(k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1460,c_664])).

cnf(c_6,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_144,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_6,c_3,c_0])).

cnf(c_843,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_826,c_144])).

cnf(c_845,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_843,c_826])).

cnf(c_639,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_145,c_144])).

cnf(c_642,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_639,c_145])).

cnf(c_846,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_845,c_7,c_642])).

cnf(c_1762,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1748,c_846])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_318,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3525,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1762,c_318])).

cnf(c_841,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_826,c_3])).

cnf(c_1303,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_841])).

cnf(c_326,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1518,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_826,c_326])).

cnf(c_2140,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_1303,c_1518])).

cnf(c_2169,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2140,c_1518])).

cnf(c_4467,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3525,c_2169])).

cnf(c_4540,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_4467,c_628])).

cnf(c_4542,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4540,c_7])).

cnf(c_4739,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4542,c_325])).

cnf(c_541,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_144])).

cnf(c_7174,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_4739,c_541])).

cnf(c_7178,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7174,c_642])).

cnf(c_3519,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_658,c_318])).

cnf(c_5956,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3519,c_0])).

cnf(c_7179,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7178,c_5956])).

cnf(c_7237,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7179,c_4542])).

cnf(c_7444,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7237,c_11])).

cnf(c_7443,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_7237,c_11])).

cnf(c_8035,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7237,c_7443])).

cnf(c_8054,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8035,c_7])).

cnf(c_8055,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_8054,c_7443])).

cnf(c_8394,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7444,c_8055])).

cnf(c_8407,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_8394,c_7])).

cnf(c_8591,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_8407,c_8055])).

cnf(c_8596,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_8591])).

cnf(c_631,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_145])).

cnf(c_14072,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_8596,c_631])).

cnf(c_12,negated_conjecture,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_143,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_12,c_3,c_0])).

cnf(c_434,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11,c_143])).

cnf(c_42032,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_14072,c_434])).

cnf(c_327,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_4730,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4542,c_327])).

cnf(c_6867,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_145,c_4730])).

cnf(c_6938,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6867,c_4542])).

cnf(c_550,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
    inference(superposition,[status(thm)],[c_144,c_11])).

cnf(c_29479,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)),X3)) ),
    inference(superposition,[status(thm)],[c_6938,c_550])).

cnf(c_29500,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_6938,c_3])).

cnf(c_29631,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_29479,c_29500])).

cnf(c_6222,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2))) = k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_145,c_541])).

cnf(c_1514,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_145,c_326])).

cnf(c_6309,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k5_xboole_0(X0,k3_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6222,c_1514])).

cnf(c_29632,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(light_normalisation,[status(thm)],[c_29631,c_6309])).

cnf(c_42033,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_42032,c_29632])).

cnf(c_544,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X1,X2),X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_144])).

cnf(c_9018,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_4542,c_544])).

cnf(c_822,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_644,c_145])).

cnf(c_6263,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X1))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_822,c_541])).

cnf(c_6280,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_6263,c_822])).

cnf(c_9046,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9018,c_4467,c_4542,c_6280,c_7237])).

cnf(c_42034,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_42033,c_7,c_9046])).

cnf(c_42035,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_42034])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.66/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.66/1.99  
% 11.66/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.66/1.99  
% 11.66/1.99  ------  iProver source info
% 11.66/1.99  
% 11.66/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.66/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.66/1.99  git: non_committed_changes: false
% 11.66/1.99  git: last_make_outside_of_git: false
% 11.66/1.99  
% 11.66/1.99  ------ 
% 11.66/1.99  
% 11.66/1.99  ------ Input Options
% 11.66/1.99  
% 11.66/1.99  --out_options                           all
% 11.66/1.99  --tptp_safe_out                         true
% 11.66/1.99  --problem_path                          ""
% 11.66/1.99  --include_path                          ""
% 11.66/1.99  --clausifier                            res/vclausify_rel
% 11.66/1.99  --clausifier_options                    ""
% 11.66/1.99  --stdin                                 false
% 11.66/1.99  --stats_out                             all
% 11.66/1.99  
% 11.66/1.99  ------ General Options
% 11.66/1.99  
% 11.66/1.99  --fof                                   false
% 11.66/1.99  --time_out_real                         305.
% 11.66/1.99  --time_out_virtual                      -1.
% 11.66/1.99  --symbol_type_check                     false
% 11.66/1.99  --clausify_out                          false
% 11.66/1.99  --sig_cnt_out                           false
% 11.66/1.99  --trig_cnt_out                          false
% 11.66/1.99  --trig_cnt_out_tolerance                1.
% 11.66/1.99  --trig_cnt_out_sk_spl                   false
% 11.66/1.99  --abstr_cl_out                          false
% 11.66/1.99  
% 11.66/1.99  ------ Global Options
% 11.66/1.99  
% 11.66/1.99  --schedule                              default
% 11.66/1.99  --add_important_lit                     false
% 11.66/1.99  --prop_solver_per_cl                    1000
% 11.66/1.99  --min_unsat_core                        false
% 11.66/1.99  --soft_assumptions                      false
% 11.66/1.99  --soft_lemma_size                       3
% 11.66/1.99  --prop_impl_unit_size                   0
% 11.66/1.99  --prop_impl_unit                        []
% 11.66/1.99  --share_sel_clauses                     true
% 11.66/1.99  --reset_solvers                         false
% 11.66/1.99  --bc_imp_inh                            [conj_cone]
% 11.66/1.99  --conj_cone_tolerance                   3.
% 11.66/1.99  --extra_neg_conj                        none
% 11.66/1.99  --large_theory_mode                     true
% 11.66/1.99  --prolific_symb_bound                   200
% 11.66/1.99  --lt_threshold                          2000
% 11.66/1.99  --clause_weak_htbl                      true
% 11.66/1.99  --gc_record_bc_elim                     false
% 11.66/1.99  
% 11.66/1.99  ------ Preprocessing Options
% 11.66/1.99  
% 11.66/1.99  --preprocessing_flag                    true
% 11.66/1.99  --time_out_prep_mult                    0.1
% 11.66/1.99  --splitting_mode                        input
% 11.66/1.99  --splitting_grd                         true
% 11.66/1.99  --splitting_cvd                         false
% 11.66/1.99  --splitting_cvd_svl                     false
% 11.66/1.99  --splitting_nvd                         32
% 11.66/1.99  --sub_typing                            true
% 11.66/1.99  --prep_gs_sim                           true
% 11.66/1.99  --prep_unflatten                        true
% 11.66/1.99  --prep_res_sim                          true
% 11.66/1.99  --prep_upred                            true
% 11.66/1.99  --prep_sem_filter                       exhaustive
% 11.66/1.99  --prep_sem_filter_out                   false
% 11.66/1.99  --pred_elim                             true
% 11.66/1.99  --res_sim_input                         true
% 11.66/1.99  --eq_ax_congr_red                       true
% 11.66/1.99  --pure_diseq_elim                       true
% 11.66/1.99  --brand_transform                       false
% 11.66/1.99  --non_eq_to_eq                          false
% 11.66/1.99  --prep_def_merge                        true
% 11.66/1.99  --prep_def_merge_prop_impl              false
% 11.66/1.99  --prep_def_merge_mbd                    true
% 11.66/1.99  --prep_def_merge_tr_red                 false
% 11.66/1.99  --prep_def_merge_tr_cl                  false
% 11.66/1.99  --smt_preprocessing                     true
% 11.66/1.99  --smt_ac_axioms                         fast
% 11.66/1.99  --preprocessed_out                      false
% 11.66/1.99  --preprocessed_stats                    false
% 11.66/1.99  
% 11.66/1.99  ------ Abstraction refinement Options
% 11.66/1.99  
% 11.66/1.99  --abstr_ref                             []
% 11.66/1.99  --abstr_ref_prep                        false
% 11.66/1.99  --abstr_ref_until_sat                   false
% 11.66/1.99  --abstr_ref_sig_restrict                funpre
% 11.66/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.66/1.99  --abstr_ref_under                       []
% 11.66/1.99  
% 11.66/1.99  ------ SAT Options
% 11.66/1.99  
% 11.66/1.99  --sat_mode                              false
% 11.66/1.99  --sat_fm_restart_options                ""
% 11.66/1.99  --sat_gr_def                            false
% 11.66/1.99  --sat_epr_types                         true
% 11.66/1.99  --sat_non_cyclic_types                  false
% 11.66/1.99  --sat_finite_models                     false
% 11.66/1.99  --sat_fm_lemmas                         false
% 11.66/1.99  --sat_fm_prep                           false
% 11.66/1.99  --sat_fm_uc_incr                        true
% 11.66/1.99  --sat_out_model                         small
% 11.66/1.99  --sat_out_clauses                       false
% 11.66/1.99  
% 11.66/1.99  ------ QBF Options
% 11.66/1.99  
% 11.66/1.99  --qbf_mode                              false
% 11.66/1.99  --qbf_elim_univ                         false
% 11.66/1.99  --qbf_dom_inst                          none
% 11.66/1.99  --qbf_dom_pre_inst                      false
% 11.66/1.99  --qbf_sk_in                             false
% 11.66/1.99  --qbf_pred_elim                         true
% 11.66/1.99  --qbf_split                             512
% 11.66/1.99  
% 11.66/1.99  ------ BMC1 Options
% 11.66/1.99  
% 11.66/1.99  --bmc1_incremental                      false
% 11.66/1.99  --bmc1_axioms                           reachable_all
% 11.66/1.99  --bmc1_min_bound                        0
% 11.66/1.99  --bmc1_max_bound                        -1
% 11.66/1.99  --bmc1_max_bound_default                -1
% 11.66/1.99  --bmc1_symbol_reachability              true
% 11.66/1.99  --bmc1_property_lemmas                  false
% 11.66/1.99  --bmc1_k_induction                      false
% 11.66/1.99  --bmc1_non_equiv_states                 false
% 11.66/1.99  --bmc1_deadlock                         false
% 11.66/1.99  --bmc1_ucm                              false
% 11.66/1.99  --bmc1_add_unsat_core                   none
% 11.66/1.99  --bmc1_unsat_core_children              false
% 11.66/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.66/1.99  --bmc1_out_stat                         full
% 11.66/1.99  --bmc1_ground_init                      false
% 11.66/1.99  --bmc1_pre_inst_next_state              false
% 11.66/1.99  --bmc1_pre_inst_state                   false
% 11.66/1.99  --bmc1_pre_inst_reach_state             false
% 11.66/1.99  --bmc1_out_unsat_core                   false
% 11.66/1.99  --bmc1_aig_witness_out                  false
% 11.66/1.99  --bmc1_verbose                          false
% 11.66/1.99  --bmc1_dump_clauses_tptp                false
% 11.66/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.66/1.99  --bmc1_dump_file                        -
% 11.66/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.66/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.66/1.99  --bmc1_ucm_extend_mode                  1
% 11.66/1.99  --bmc1_ucm_init_mode                    2
% 11.66/1.99  --bmc1_ucm_cone_mode                    none
% 11.66/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.66/1.99  --bmc1_ucm_relax_model                  4
% 11.66/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.66/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.66/1.99  --bmc1_ucm_layered_model                none
% 11.66/1.99  --bmc1_ucm_max_lemma_size               10
% 11.66/1.99  
% 11.66/1.99  ------ AIG Options
% 11.66/1.99  
% 11.66/1.99  --aig_mode                              false
% 11.66/1.99  
% 11.66/1.99  ------ Instantiation Options
% 11.66/1.99  
% 11.66/1.99  --instantiation_flag                    true
% 11.66/1.99  --inst_sos_flag                         true
% 11.66/1.99  --inst_sos_phase                        true
% 11.66/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.66/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.66/1.99  --inst_lit_sel_side                     num_symb
% 11.66/1.99  --inst_solver_per_active                1400
% 11.66/1.99  --inst_solver_calls_frac                1.
% 11.66/1.99  --inst_passive_queue_type               priority_queues
% 11.66/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.66/1.99  --inst_passive_queues_freq              [25;2]
% 11.66/1.99  --inst_dismatching                      true
% 11.66/1.99  --inst_eager_unprocessed_to_passive     true
% 11.66/1.99  --inst_prop_sim_given                   true
% 11.66/1.99  --inst_prop_sim_new                     false
% 11.66/1.99  --inst_subs_new                         false
% 11.66/1.99  --inst_eq_res_simp                      false
% 11.66/1.99  --inst_subs_given                       false
% 11.66/1.99  --inst_orphan_elimination               true
% 11.66/1.99  --inst_learning_loop_flag               true
% 11.66/1.99  --inst_learning_start                   3000
% 11.66/1.99  --inst_learning_factor                  2
% 11.66/1.99  --inst_start_prop_sim_after_learn       3
% 11.66/1.99  --inst_sel_renew                        solver
% 11.66/1.99  --inst_lit_activity_flag                true
% 11.66/1.99  --inst_restr_to_given                   false
% 11.66/1.99  --inst_activity_threshold               500
% 11.66/1.99  --inst_out_proof                        true
% 11.66/1.99  
% 11.66/1.99  ------ Resolution Options
% 11.66/1.99  
% 11.66/1.99  --resolution_flag                       true
% 11.66/1.99  --res_lit_sel                           adaptive
% 11.66/1.99  --res_lit_sel_side                      none
% 11.66/1.99  --res_ordering                          kbo
% 11.66/1.99  --res_to_prop_solver                    active
% 11.66/1.99  --res_prop_simpl_new                    false
% 11.66/1.99  --res_prop_simpl_given                  true
% 11.66/1.99  --res_passive_queue_type                priority_queues
% 11.66/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.66/1.99  --res_passive_queues_freq               [15;5]
% 11.66/1.99  --res_forward_subs                      full
% 11.66/1.99  --res_backward_subs                     full
% 11.66/1.99  --res_forward_subs_resolution           true
% 11.66/1.99  --res_backward_subs_resolution          true
% 11.66/1.99  --res_orphan_elimination                true
% 11.66/1.99  --res_time_limit                        2.
% 11.66/1.99  --res_out_proof                         true
% 11.66/1.99  
% 11.66/1.99  ------ Superposition Options
% 11.66/1.99  
% 11.66/1.99  --superposition_flag                    true
% 11.66/1.99  --sup_passive_queue_type                priority_queues
% 11.66/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.66/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.66/1.99  --demod_completeness_check              fast
% 11.66/1.99  --demod_use_ground                      true
% 11.66/1.99  --sup_to_prop_solver                    passive
% 11.66/1.99  --sup_prop_simpl_new                    true
% 11.66/1.99  --sup_prop_simpl_given                  true
% 11.66/1.99  --sup_fun_splitting                     true
% 11.66/1.99  --sup_smt_interval                      50000
% 11.66/1.99  
% 11.66/1.99  ------ Superposition Simplification Setup
% 11.66/1.99  
% 11.66/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.66/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.66/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.66/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.66/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.66/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.66/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.66/1.99  --sup_immed_triv                        [TrivRules]
% 11.66/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/1.99  --sup_immed_bw_main                     []
% 11.66/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.66/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.66/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/1.99  --sup_input_bw                          []
% 11.66/1.99  
% 11.66/1.99  ------ Combination Options
% 11.66/1.99  
% 11.66/1.99  --comb_res_mult                         3
% 11.66/1.99  --comb_sup_mult                         2
% 11.66/1.99  --comb_inst_mult                        10
% 11.66/1.99  
% 11.66/1.99  ------ Debug Options
% 11.66/1.99  
% 11.66/1.99  --dbg_backtrace                         false
% 11.66/1.99  --dbg_dump_prop_clauses                 false
% 11.66/1.99  --dbg_dump_prop_clauses_file            -
% 11.66/1.99  --dbg_out_stat                          false
% 11.66/1.99  ------ Parsing...
% 11.66/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.66/1.99  
% 11.66/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.66/1.99  
% 11.66/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.66/1.99  
% 11.66/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.66/1.99  ------ Proving...
% 11.66/1.99  ------ Problem Properties 
% 11.66/1.99  
% 11.66/1.99  
% 11.66/1.99  clauses                                 13
% 11.66/1.99  conjectures                             1
% 11.66/1.99  EPR                                     0
% 11.66/1.99  Horn                                    13
% 11.66/1.99  unary                                   9
% 11.66/1.99  binary                                  4
% 11.66/1.99  lits                                    17
% 11.66/1.99  lits eq                                 12
% 11.66/1.99  fd_pure                                 0
% 11.66/1.99  fd_pseudo                               0
% 11.66/1.99  fd_cond                                 0
% 11.66/1.99  fd_pseudo_cond                          0
% 11.66/1.99  AC symbols                              1
% 11.66/1.99  
% 11.66/1.99  ------ Schedule dynamic 5 is on 
% 11.66/1.99  
% 11.66/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.66/1.99  
% 11.66/1.99  
% 11.66/1.99  ------ 
% 11.66/1.99  Current options:
% 11.66/1.99  ------ 
% 11.66/1.99  
% 11.66/1.99  ------ Input Options
% 11.66/1.99  
% 11.66/1.99  --out_options                           all
% 11.66/1.99  --tptp_safe_out                         true
% 11.66/1.99  --problem_path                          ""
% 11.66/1.99  --include_path                          ""
% 11.66/1.99  --clausifier                            res/vclausify_rel
% 11.66/1.99  --clausifier_options                    ""
% 11.66/1.99  --stdin                                 false
% 11.66/1.99  --stats_out                             all
% 11.66/1.99  
% 11.66/1.99  ------ General Options
% 11.66/1.99  
% 11.66/1.99  --fof                                   false
% 11.66/1.99  --time_out_real                         305.
% 11.66/1.99  --time_out_virtual                      -1.
% 11.66/1.99  --symbol_type_check                     false
% 11.66/1.99  --clausify_out                          false
% 11.66/1.99  --sig_cnt_out                           false
% 11.66/1.99  --trig_cnt_out                          false
% 11.66/1.99  --trig_cnt_out_tolerance                1.
% 11.66/1.99  --trig_cnt_out_sk_spl                   false
% 11.66/1.99  --abstr_cl_out                          false
% 11.66/1.99  
% 11.66/1.99  ------ Global Options
% 11.66/1.99  
% 11.66/1.99  --schedule                              default
% 11.66/1.99  --add_important_lit                     false
% 11.66/1.99  --prop_solver_per_cl                    1000
% 11.66/1.99  --min_unsat_core                        false
% 11.66/1.99  --soft_assumptions                      false
% 11.66/1.99  --soft_lemma_size                       3
% 11.66/1.99  --prop_impl_unit_size                   0
% 11.66/1.99  --prop_impl_unit                        []
% 11.66/1.99  --share_sel_clauses                     true
% 11.66/1.99  --reset_solvers                         false
% 11.66/1.99  --bc_imp_inh                            [conj_cone]
% 11.66/1.99  --conj_cone_tolerance                   3.
% 11.66/1.99  --extra_neg_conj                        none
% 11.66/1.99  --large_theory_mode                     true
% 11.66/1.99  --prolific_symb_bound                   200
% 11.66/1.99  --lt_threshold                          2000
% 11.66/1.99  --clause_weak_htbl                      true
% 11.66/1.99  --gc_record_bc_elim                     false
% 11.66/1.99  
% 11.66/1.99  ------ Preprocessing Options
% 11.66/1.99  
% 11.66/1.99  --preprocessing_flag                    true
% 11.66/1.99  --time_out_prep_mult                    0.1
% 11.66/1.99  --splitting_mode                        input
% 11.66/1.99  --splitting_grd                         true
% 11.66/1.99  --splitting_cvd                         false
% 11.66/1.99  --splitting_cvd_svl                     false
% 11.66/1.99  --splitting_nvd                         32
% 11.66/1.99  --sub_typing                            true
% 11.66/1.99  --prep_gs_sim                           true
% 11.66/1.99  --prep_unflatten                        true
% 11.66/1.99  --prep_res_sim                          true
% 11.66/1.99  --prep_upred                            true
% 11.66/1.99  --prep_sem_filter                       exhaustive
% 11.66/1.99  --prep_sem_filter_out                   false
% 11.66/1.99  --pred_elim                             true
% 11.66/1.99  --res_sim_input                         true
% 11.66/1.99  --eq_ax_congr_red                       true
% 11.66/1.99  --pure_diseq_elim                       true
% 11.66/1.99  --brand_transform                       false
% 11.66/1.99  --non_eq_to_eq                          false
% 11.66/1.99  --prep_def_merge                        true
% 11.66/1.99  --prep_def_merge_prop_impl              false
% 11.66/1.99  --prep_def_merge_mbd                    true
% 11.66/1.99  --prep_def_merge_tr_red                 false
% 11.66/1.99  --prep_def_merge_tr_cl                  false
% 11.66/1.99  --smt_preprocessing                     true
% 11.66/1.99  --smt_ac_axioms                         fast
% 11.66/1.99  --preprocessed_out                      false
% 11.66/1.99  --preprocessed_stats                    false
% 11.66/1.99  
% 11.66/1.99  ------ Abstraction refinement Options
% 11.66/1.99  
% 11.66/1.99  --abstr_ref                             []
% 11.66/1.99  --abstr_ref_prep                        false
% 11.66/1.99  --abstr_ref_until_sat                   false
% 11.66/1.99  --abstr_ref_sig_restrict                funpre
% 11.66/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.66/1.99  --abstr_ref_under                       []
% 11.66/1.99  
% 11.66/1.99  ------ SAT Options
% 11.66/1.99  
% 11.66/1.99  --sat_mode                              false
% 11.66/1.99  --sat_fm_restart_options                ""
% 11.66/1.99  --sat_gr_def                            false
% 11.66/1.99  --sat_epr_types                         true
% 11.66/1.99  --sat_non_cyclic_types                  false
% 11.66/1.99  --sat_finite_models                     false
% 11.66/1.99  --sat_fm_lemmas                         false
% 11.66/1.99  --sat_fm_prep                           false
% 11.66/1.99  --sat_fm_uc_incr                        true
% 11.66/1.99  --sat_out_model                         small
% 11.66/1.99  --sat_out_clauses                       false
% 11.66/1.99  
% 11.66/1.99  ------ QBF Options
% 11.66/1.99  
% 11.66/1.99  --qbf_mode                              false
% 11.66/1.99  --qbf_elim_univ                         false
% 11.66/1.99  --qbf_dom_inst                          none
% 11.66/1.99  --qbf_dom_pre_inst                      false
% 11.66/1.99  --qbf_sk_in                             false
% 11.66/1.99  --qbf_pred_elim                         true
% 11.66/1.99  --qbf_split                             512
% 11.66/1.99  
% 11.66/1.99  ------ BMC1 Options
% 11.66/1.99  
% 11.66/1.99  --bmc1_incremental                      false
% 11.66/1.99  --bmc1_axioms                           reachable_all
% 11.66/1.99  --bmc1_min_bound                        0
% 11.66/1.99  --bmc1_max_bound                        -1
% 11.66/1.99  --bmc1_max_bound_default                -1
% 11.66/1.99  --bmc1_symbol_reachability              true
% 11.66/1.99  --bmc1_property_lemmas                  false
% 11.66/1.99  --bmc1_k_induction                      false
% 11.66/1.99  --bmc1_non_equiv_states                 false
% 11.66/1.99  --bmc1_deadlock                         false
% 11.66/1.99  --bmc1_ucm                              false
% 11.66/1.99  --bmc1_add_unsat_core                   none
% 11.66/1.99  --bmc1_unsat_core_children              false
% 11.66/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.66/1.99  --bmc1_out_stat                         full
% 11.66/1.99  --bmc1_ground_init                      false
% 11.66/1.99  --bmc1_pre_inst_next_state              false
% 11.66/1.99  --bmc1_pre_inst_state                   false
% 11.66/1.99  --bmc1_pre_inst_reach_state             false
% 11.66/1.99  --bmc1_out_unsat_core                   false
% 11.66/1.99  --bmc1_aig_witness_out                  false
% 11.66/1.99  --bmc1_verbose                          false
% 11.66/1.99  --bmc1_dump_clauses_tptp                false
% 11.66/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.66/1.99  --bmc1_dump_file                        -
% 11.66/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.66/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.66/1.99  --bmc1_ucm_extend_mode                  1
% 11.66/1.99  --bmc1_ucm_init_mode                    2
% 11.66/1.99  --bmc1_ucm_cone_mode                    none
% 11.66/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.66/1.99  --bmc1_ucm_relax_model                  4
% 11.66/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.66/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.66/1.99  --bmc1_ucm_layered_model                none
% 11.66/1.99  --bmc1_ucm_max_lemma_size               10
% 11.66/1.99  
% 11.66/1.99  ------ AIG Options
% 11.66/1.99  
% 11.66/1.99  --aig_mode                              false
% 11.66/1.99  
% 11.66/1.99  ------ Instantiation Options
% 11.66/1.99  
% 11.66/1.99  --instantiation_flag                    true
% 11.66/1.99  --inst_sos_flag                         true
% 11.66/1.99  --inst_sos_phase                        true
% 11.66/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.66/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.66/1.99  --inst_lit_sel_side                     none
% 11.66/1.99  --inst_solver_per_active                1400
% 11.66/1.99  --inst_solver_calls_frac                1.
% 11.66/1.99  --inst_passive_queue_type               priority_queues
% 11.66/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.66/1.99  --inst_passive_queues_freq              [25;2]
% 11.66/1.99  --inst_dismatching                      true
% 11.66/1.99  --inst_eager_unprocessed_to_passive     true
% 11.66/1.99  --inst_prop_sim_given                   true
% 11.66/1.99  --inst_prop_sim_new                     false
% 11.66/1.99  --inst_subs_new                         false
% 11.66/1.99  --inst_eq_res_simp                      false
% 11.66/1.99  --inst_subs_given                       false
% 11.66/1.99  --inst_orphan_elimination               true
% 11.66/1.99  --inst_learning_loop_flag               true
% 11.66/1.99  --inst_learning_start                   3000
% 11.66/1.99  --inst_learning_factor                  2
% 11.66/1.99  --inst_start_prop_sim_after_learn       3
% 11.66/1.99  --inst_sel_renew                        solver
% 11.66/1.99  --inst_lit_activity_flag                true
% 11.66/1.99  --inst_restr_to_given                   false
% 11.66/1.99  --inst_activity_threshold               500
% 11.66/1.99  --inst_out_proof                        true
% 11.66/1.99  
% 11.66/1.99  ------ Resolution Options
% 11.66/1.99  
% 11.66/1.99  --resolution_flag                       false
% 11.66/1.99  --res_lit_sel                           adaptive
% 11.66/1.99  --res_lit_sel_side                      none
% 11.66/1.99  --res_ordering                          kbo
% 11.66/1.99  --res_to_prop_solver                    active
% 11.66/1.99  --res_prop_simpl_new                    false
% 11.66/1.99  --res_prop_simpl_given                  true
% 11.66/1.99  --res_passive_queue_type                priority_queues
% 11.66/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.66/1.99  --res_passive_queues_freq               [15;5]
% 11.66/1.99  --res_forward_subs                      full
% 11.66/1.99  --res_backward_subs                     full
% 11.66/1.99  --res_forward_subs_resolution           true
% 11.66/1.99  --res_backward_subs_resolution          true
% 11.66/1.99  --res_orphan_elimination                true
% 11.66/1.99  --res_time_limit                        2.
% 11.66/1.99  --res_out_proof                         true
% 11.66/1.99  
% 11.66/1.99  ------ Superposition Options
% 11.66/1.99  
% 11.66/1.99  --superposition_flag                    true
% 11.66/1.99  --sup_passive_queue_type                priority_queues
% 11.66/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.66/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.66/1.99  --demod_completeness_check              fast
% 11.66/1.99  --demod_use_ground                      true
% 11.66/1.99  --sup_to_prop_solver                    passive
% 11.66/1.99  --sup_prop_simpl_new                    true
% 11.66/1.99  --sup_prop_simpl_given                  true
% 11.66/1.99  --sup_fun_splitting                     true
% 11.66/1.99  --sup_smt_interval                      50000
% 11.66/1.99  
% 11.66/1.99  ------ Superposition Simplification Setup
% 11.66/1.99  
% 11.66/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.66/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.66/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.66/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.66/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.66/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.66/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.66/1.99  --sup_immed_triv                        [TrivRules]
% 11.66/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/1.99  --sup_immed_bw_main                     []
% 11.66/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.66/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.66/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.66/2.00  --sup_input_bw                          []
% 11.66/2.00  
% 11.66/2.00  ------ Combination Options
% 11.66/2.00  
% 11.66/2.00  --comb_res_mult                         3
% 11.66/2.00  --comb_sup_mult                         2
% 11.66/2.00  --comb_inst_mult                        10
% 11.66/2.00  
% 11.66/2.00  ------ Debug Options
% 11.66/2.00  
% 11.66/2.00  --dbg_backtrace                         false
% 11.66/2.00  --dbg_dump_prop_clauses                 false
% 11.66/2.00  --dbg_dump_prop_clauses_file            -
% 11.66/2.00  --dbg_out_stat                          false
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  ------ Proving...
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  % SZS status Theorem for theBenchmark.p
% 11.66/2.00  
% 11.66/2.00   Resolution empty clause
% 11.66/2.00  
% 11.66/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.66/2.00  
% 11.66/2.00  fof(f11,axiom,(
% 11.66/2.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f32,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f11])).
% 11.66/2.00  
% 11.66/2.00  fof(f5,axiom,(
% 11.66/2.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f25,plain,(
% 11.66/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 11.66/2.00    inference(cnf_transformation,[],[f5])).
% 11.66/2.00  
% 11.66/2.00  fof(f12,axiom,(
% 11.66/2.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f33,plain,(
% 11.66/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f12])).
% 11.66/2.00  
% 11.66/2.00  fof(f3,axiom,(
% 11.66/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f23,plain,(
% 11.66/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.66/2.00    inference(cnf_transformation,[],[f3])).
% 11.66/2.00  
% 11.66/2.00  fof(f35,plain,(
% 11.66/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 11.66/2.00    inference(definition_unfolding,[],[f33,f23])).
% 11.66/2.00  
% 11.66/2.00  fof(f36,plain,(
% 11.66/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 11.66/2.00    inference(definition_unfolding,[],[f25,f35])).
% 11.66/2.00  
% 11.66/2.00  fof(f4,axiom,(
% 11.66/2.00    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f24,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f4])).
% 11.66/2.00  
% 11.66/2.00  fof(f1,axiom,(
% 11.66/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f20,plain,(
% 11.66/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f1])).
% 11.66/2.00  
% 11.66/2.00  fof(f6,axiom,(
% 11.66/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f26,plain,(
% 11.66/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.66/2.00    inference(cnf_transformation,[],[f6])).
% 11.66/2.00  
% 11.66/2.00  fof(f37,plain,(
% 11.66/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 11.66/2.00    inference(definition_unfolding,[],[f26,f23,f23])).
% 11.66/2.00  
% 11.66/2.00  fof(f8,axiom,(
% 11.66/2.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f28,plain,(
% 11.66/2.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.66/2.00    inference(cnf_transformation,[],[f8])).
% 11.66/2.00  
% 11.66/2.00  fof(f10,axiom,(
% 11.66/2.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f31,plain,(
% 11.66/2.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f10])).
% 11.66/2.00  
% 11.66/2.00  fof(f41,plain,(
% 11.66/2.00    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1)) )),
% 11.66/2.00    inference(definition_unfolding,[],[f31,f23])).
% 11.66/2.00  
% 11.66/2.00  fof(f7,axiom,(
% 11.66/2.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f27,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f7])).
% 11.66/2.00  
% 11.66/2.00  fof(f38,plain,(
% 11.66/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 11.66/2.00    inference(definition_unfolding,[],[f27,f23,f23])).
% 11.66/2.00  
% 11.66/2.00  fof(f2,axiom,(
% 11.66/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f16,plain,(
% 11.66/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.66/2.00    inference(nnf_transformation,[],[f2])).
% 11.66/2.00  
% 11.66/2.00  fof(f21,plain,(
% 11.66/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.66/2.00    inference(cnf_transformation,[],[f16])).
% 11.66/2.00  
% 11.66/2.00  fof(f13,conjecture,(
% 11.66/2.00    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 11.66/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.66/2.00  
% 11.66/2.00  fof(f14,negated_conjecture,(
% 11.66/2.00    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 11.66/2.00    inference(negated_conjecture,[],[f13])).
% 11.66/2.00  
% 11.66/2.00  fof(f15,plain,(
% 11.66/2.00    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)),
% 11.66/2.00    inference(ennf_transformation,[],[f14])).
% 11.66/2.00  
% 11.66/2.00  fof(f18,plain,(
% 11.66/2.00    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 11.66/2.00    introduced(choice_axiom,[])).
% 11.66/2.00  
% 11.66/2.00  fof(f19,plain,(
% 11.66/2.00    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 11.66/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).
% 11.66/2.00  
% 11.66/2.00  fof(f34,plain,(
% 11.66/2.00    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 11.66/2.00    inference(cnf_transformation,[],[f19])).
% 11.66/2.00  
% 11.66/2.00  fof(f42,plain,(
% 11.66/2.00    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 11.66/2.00    inference(definition_unfolding,[],[f34,f23,f35])).
% 11.66/2.00  
% 11.66/2.00  cnf(c_11,plain,
% 11.66/2.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 11.66/2.00      inference(cnf_transformation,[],[f32]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 11.66/2.00      inference(cnf_transformation,[],[f36]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3,plain,
% 11.66/2.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 11.66/2.00      inference(cnf_transformation,[],[f24]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_0,plain,
% 11.66/2.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.66/2.00      inference(cnf_transformation,[],[f20]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_145,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 11.66/2.00      inference(theory_normalisation,[status(thm)],[c_4,c_3,c_0]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_5,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.66/2.00      inference(cnf_transformation,[],[f37]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_636,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_145,c_5]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_644,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_636,c_145]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_7,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.66/2.00      inference(cnf_transformation,[],[f28]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_436,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_7,c_11]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_628,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_436,c_145]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_824,plain,
% 11.66/2.00      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_644,c_628]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_826,plain,
% 11.66/2.00      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_824,c_7]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_325,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1460,plain,
% 11.66/2.00      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_826,c_325]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_10,plain,
% 11.66/2.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) ),
% 11.66/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_315,plain,
% 11.66/2.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1) = iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_658,plain,
% 11.66/2.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_315,c_5]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_664,plain,
% 11.66/2.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_0,c_658]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1748,plain,
% 11.66/2.00      ( r1_xboole_0(k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_1460,c_664]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_6,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.66/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_144,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.66/2.00      inference(theory_normalisation,[status(thm)],[c_6,c_3,c_0]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_843,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_826,c_144]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_845,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_843,c_826]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_639,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_145,c_144]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_642,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_639,c_145]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_846,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_845,c_7,c_642]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1762,plain,
% 11.66/2.00      ( r1_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_1748,c_846]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_2,plain,
% 11.66/2.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.66/2.00      inference(cnf_transformation,[],[f21]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_318,plain,
% 11.66/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 11.66/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3525,plain,
% 11.66/2.00      ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_1762,c_318]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_841,plain,
% 11.66/2.00      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_826,c_3]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1303,plain,
% 11.66/2.00      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_0,c_841]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_326,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1518,plain,
% 11.66/2.00      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_826,c_326]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_2140,plain,
% 11.66/2.00      ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_1303,c_1518]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_2169,plain,
% 11.66/2.00      ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_2140,c_1518]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4467,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_3525,c_2169]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4540,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_4467,c_628]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4542,plain,
% 11.66/2.00      ( k3_xboole_0(X0,X0) = X0 ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_4540,c_7]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4739,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_4542,c_325]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_541,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_0,c_144]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_7174,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_4739,c_541]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_7178,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_7174,c_642]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_3519,plain,
% 11.66/2.00      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_658,c_318]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_5956,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_3519,c_0]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_7179,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k1_xboole_0 ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_7178,c_5956]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_7237,plain,
% 11.66/2.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_7179,c_4542]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_7444,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_7237,c_11]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_7443,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_7237,c_11]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_8035,plain,
% 11.66/2.00      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_7237,c_7443]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_8054,plain,
% 11.66/2.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_8035,c_7]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_8055,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_8054,c_7443]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_8394,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_7444,c_8055]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_8407,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_8394,c_7]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_8591,plain,
% 11.66/2.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_8407,c_8055]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_8596,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_11,c_8591]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_631,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_0,c_145]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_14072,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_8596,c_631]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_12,negated_conjecture,
% 11.66/2.00      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
% 11.66/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_143,negated_conjecture,
% 11.66/2.00      ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
% 11.66/2.00      inference(theory_normalisation,[status(thm)],[c_12,c_3,c_0]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_434,plain,
% 11.66/2.00      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_11,c_143]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_42032,plain,
% 11.66/2.00      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_14072,c_434]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_327,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_4730,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_4542,c_327]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_6867,plain,
% 11.66/2.00      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = k3_xboole_0(X0,X0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_145,c_4730]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_6938,plain,
% 11.66/2.00      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),X0) = X0 ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_6867,c_4542]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_550,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_144,c_11]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_29479,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)),X3)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_6938,c_550]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_29500,plain,
% 11.66/2.00      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,X2) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_6938,c_3]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_29631,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))),X3) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X2),X3)) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_29479,c_29500]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_6222,plain,
% 11.66/2.00      ( k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2))) = k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_145,c_541]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_1514,plain,
% 11.66/2.00      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,X0) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_145,c_326]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_6309,plain,
% 11.66/2.00      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k5_xboole_0(X0,k3_xboole_0(X2,X0)) ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_6222,c_1514]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_29632,plain,
% 11.66/2.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 11.66/2.00      inference(light_normalisation,[status(thm)],[c_29631,c_6309]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_42033,plain,
% 11.66/2.00      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))) != k5_xboole_0(sK0,sK1) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_42032,c_29632]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_544,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X1,X2),X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_0,c_144]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_9018,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_4542,c_544]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_822,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) = X0 ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_644,c_145]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_6263,plain,
% 11.66/2.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X1))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
% 11.66/2.00      inference(superposition,[status(thm)],[c_822,c_541]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_6280,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_6263,c_822]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_9046,plain,
% 11.66/2.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.66/2.00      inference(demodulation,
% 11.66/2.00                [status(thm)],
% 11.66/2.00                [c_9018,c_4467,c_4542,c_6280,c_7237]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_42034,plain,
% 11.66/2.00      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
% 11.66/2.00      inference(demodulation,[status(thm)],[c_42033,c_7,c_9046]) ).
% 11.66/2.00  
% 11.66/2.00  cnf(c_42035,plain,
% 11.66/2.00      ( $false ),
% 11.66/2.00      inference(equality_resolution_simp,[status(thm)],[c_42034]) ).
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.66/2.00  
% 11.66/2.00  ------                               Statistics
% 11.66/2.00  
% 11.66/2.00  ------ General
% 11.66/2.00  
% 11.66/2.00  abstr_ref_over_cycles:                  0
% 11.66/2.00  abstr_ref_under_cycles:                 0
% 11.66/2.00  gc_basic_clause_elim:                   0
% 11.66/2.00  forced_gc_time:                         0
% 11.66/2.00  parsing_time:                           0.007
% 11.66/2.00  unif_index_cands_time:                  0.
% 11.66/2.00  unif_index_add_time:                    0.
% 11.66/2.00  orderings_time:                         0.
% 11.66/2.00  out_proof_time:                         0.009
% 11.66/2.00  total_time:                             1.222
% 11.66/2.00  num_of_symbols:                         37
% 11.66/2.00  num_of_terms:                           60479
% 11.66/2.00  
% 11.66/2.00  ------ Preprocessing
% 11.66/2.00  
% 11.66/2.00  num_of_splits:                          0
% 11.66/2.00  num_of_split_atoms:                     0
% 11.66/2.00  num_of_reused_defs:                     0
% 11.66/2.00  num_eq_ax_congr_red:                    2
% 11.66/2.00  num_of_sem_filtered_clauses:            1
% 11.66/2.00  num_of_subtypes:                        0
% 11.66/2.00  monotx_restored_types:                  0
% 11.66/2.00  sat_num_of_epr_types:                   0
% 11.66/2.00  sat_num_of_non_cyclic_types:            0
% 11.66/2.00  sat_guarded_non_collapsed_types:        0
% 11.66/2.00  num_pure_diseq_elim:                    0
% 11.66/2.00  simp_replaced_by:                       0
% 11.66/2.00  res_preprocessed:                       50
% 11.66/2.00  prep_upred:                             0
% 11.66/2.00  prep_unflattend:                        4
% 11.66/2.00  smt_new_axioms:                         0
% 11.66/2.00  pred_elim_cands:                        1
% 11.66/2.00  pred_elim:                              0
% 11.66/2.00  pred_elim_cl:                           0
% 11.66/2.00  pred_elim_cycles:                       1
% 11.66/2.00  merged_defs:                            12
% 11.66/2.00  merged_defs_ncl:                        0
% 11.66/2.00  bin_hyper_res:                          12
% 11.66/2.00  prep_cycles:                            3
% 11.66/2.00  pred_elim_time:                         0.
% 11.66/2.00  splitting_time:                         0.
% 11.66/2.00  sem_filter_time:                        0.
% 11.66/2.00  monotx_time:                            0.
% 11.66/2.00  subtype_inf_time:                       0.
% 11.66/2.00  
% 11.66/2.00  ------ Problem properties
% 11.66/2.00  
% 11.66/2.00  clauses:                                13
% 11.66/2.00  conjectures:                            1
% 11.66/2.00  epr:                                    0
% 11.66/2.00  horn:                                   13
% 11.66/2.00  ground:                                 1
% 11.66/2.00  unary:                                  9
% 11.66/2.00  binary:                                 4
% 11.66/2.00  lits:                                   17
% 11.66/2.00  lits_eq:                                12
% 11.66/2.00  fd_pure:                                0
% 11.66/2.00  fd_pseudo:                              0
% 11.66/2.00  fd_cond:                                0
% 11.66/2.00  fd_pseudo_cond:                         0
% 11.66/2.00  ac_symbols:                             2
% 11.66/2.00  
% 11.66/2.00  ------ Propositional Solver
% 11.66/2.00  
% 11.66/2.00  prop_solver_calls:                      28
% 11.66/2.00  prop_fast_solver_calls:                 485
% 11.66/2.00  smt_solver_calls:                       0
% 11.66/2.00  smt_fast_solver_calls:                  0
% 11.66/2.00  prop_num_of_clauses:                    9225
% 11.66/2.00  prop_preprocess_simplified:             12262
% 11.66/2.00  prop_fo_subsumed:                       0
% 11.66/2.00  prop_solver_time:                       0.
% 11.66/2.00  smt_solver_time:                        0.
% 11.66/2.00  smt_fast_solver_time:                   0.
% 11.66/2.00  prop_fast_solver_time:                  0.
% 11.66/2.00  prop_unsat_core_time:                   0.
% 11.66/2.00  
% 11.66/2.00  ------ QBF
% 11.66/2.00  
% 11.66/2.00  qbf_q_res:                              0
% 11.66/2.00  qbf_num_tautologies:                    0
% 11.66/2.00  qbf_prep_cycles:                        0
% 11.66/2.00  
% 11.66/2.00  ------ BMC1
% 11.66/2.00  
% 11.66/2.00  bmc1_current_bound:                     -1
% 11.66/2.00  bmc1_last_solved_bound:                 -1
% 11.66/2.00  bmc1_unsat_core_size:                   -1
% 11.66/2.00  bmc1_unsat_core_parents_size:           -1
% 11.66/2.00  bmc1_merge_next_fun:                    0
% 11.66/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.66/2.00  
% 11.66/2.00  ------ Instantiation
% 11.66/2.00  
% 11.66/2.00  inst_num_of_clauses:                    2501
% 11.66/2.00  inst_num_in_passive:                    595
% 11.66/2.00  inst_num_in_active:                     883
% 11.66/2.00  inst_num_in_unprocessed:                1023
% 11.66/2.00  inst_num_of_loops:                      940
% 11.66/2.00  inst_num_of_learning_restarts:          0
% 11.66/2.00  inst_num_moves_active_passive:          51
% 11.66/2.00  inst_lit_activity:                      0
% 11.66/2.00  inst_lit_activity_moves:                0
% 11.66/2.00  inst_num_tautologies:                   0
% 11.66/2.00  inst_num_prop_implied:                  0
% 11.66/2.00  inst_num_existing_simplified:           0
% 11.66/2.00  inst_num_eq_res_simplified:             0
% 11.66/2.00  inst_num_child_elim:                    0
% 11.66/2.00  inst_num_of_dismatching_blockings:      3544
% 11.66/2.00  inst_num_of_non_proper_insts:           5359
% 11.66/2.00  inst_num_of_duplicates:                 0
% 11.66/2.00  inst_inst_num_from_inst_to_res:         0
% 11.66/2.00  inst_dismatching_checking_time:         0.
% 11.66/2.00  
% 11.66/2.00  ------ Resolution
% 11.66/2.00  
% 11.66/2.00  res_num_of_clauses:                     0
% 11.66/2.00  res_num_in_passive:                     0
% 11.66/2.00  res_num_in_active:                      0
% 11.66/2.00  res_num_of_loops:                       53
% 11.66/2.00  res_forward_subset_subsumed:            880
% 11.66/2.00  res_backward_subset_subsumed:           6
% 11.66/2.00  res_forward_subsumed:                   0
% 11.66/2.00  res_backward_subsumed:                  0
% 11.66/2.00  res_forward_subsumption_resolution:     0
% 11.66/2.00  res_backward_subsumption_resolution:    0
% 11.66/2.00  res_clause_to_clause_subsumption:       46919
% 11.66/2.00  res_orphan_elimination:                 0
% 11.66/2.00  res_tautology_del:                      604
% 11.66/2.00  res_num_eq_res_simplified:              0
% 11.66/2.00  res_num_sel_changes:                    0
% 11.66/2.00  res_moves_from_active_to_pass:          0
% 11.66/2.00  
% 11.66/2.00  ------ Superposition
% 11.66/2.00  
% 11.66/2.00  sup_time_total:                         0.
% 11.66/2.00  sup_time_generating:                    0.
% 11.66/2.00  sup_time_sim_full:                      0.
% 11.66/2.00  sup_time_sim_immed:                     0.
% 11.66/2.00  
% 11.66/2.00  sup_num_of_clauses:                     2867
% 11.66/2.00  sup_num_in_active:                      134
% 11.66/2.00  sup_num_in_passive:                     2733
% 11.66/2.00  sup_num_of_loops:                       187
% 11.66/2.00  sup_fw_superposition:                   8581
% 11.66/2.00  sup_bw_superposition:                   5906
% 11.66/2.00  sup_immediate_simplified:               6883
% 11.66/2.00  sup_given_eliminated:                   6
% 11.66/2.00  comparisons_done:                       0
% 11.66/2.00  comparisons_avoided:                    0
% 11.66/2.00  
% 11.66/2.00  ------ Simplifications
% 11.66/2.00  
% 11.66/2.00  
% 11.66/2.00  sim_fw_subset_subsumed:                 34
% 11.66/2.00  sim_bw_subset_subsumed:                 0
% 11.66/2.00  sim_fw_subsumed:                        817
% 11.66/2.00  sim_bw_subsumed:                        30
% 11.66/2.00  sim_fw_subsumption_res:                 0
% 11.66/2.00  sim_bw_subsumption_res:                 0
% 11.66/2.00  sim_tautology_del:                      0
% 11.66/2.00  sim_eq_tautology_del:                   1753
% 11.66/2.00  sim_eq_res_simp:                        1
% 11.66/2.00  sim_fw_demodulated:                     5451
% 11.66/2.00  sim_bw_demodulated:                     97
% 11.66/2.00  sim_light_normalised:                   2839
% 11.66/2.00  sim_joinable_taut:                      162
% 11.66/2.00  sim_joinable_simp:                      0
% 11.66/2.00  sim_ac_normalised:                      0
% 11.66/2.00  sim_smt_subsumption:                    0
% 11.66/2.00  
%------------------------------------------------------------------------------
