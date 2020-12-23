%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:01 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  103 (4838 expanded)
%              Number of clauses        :   73 (2126 expanded)
%              Number of leaves         :   14 (1285 expanded)
%              Depth                    :   23
%              Number of atoms          :  124 (4859 expanded)
%              Number of equality atoms :  107 (4842 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f29,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f31,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f29,f19,f19,f23])).

cnf(c_6,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_220,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_221,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6132,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_220,c_221])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_218,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6549,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_6132,c_218])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_6716,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6549,c_3])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_81,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_5,c_4,c_0])).

cnf(c_496,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_81,c_2])).

cnf(c_512,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_496,c_0])).

cnf(c_568,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_512,c_2])).

cnf(c_577,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_568,c_4])).

cnf(c_620,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_577])).

cnf(c_681,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_577,c_620])).

cnf(c_692,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_681,c_568])).

cnf(c_750,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_692])).

cnf(c_227,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_875,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_568,c_227])).

cnf(c_932,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_750,c_875])).

cnf(c_934,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_875,c_692])).

cnf(c_935,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_875,c_4])).

cnf(c_684,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_620,c_4])).

cnf(c_690,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_684,c_4])).

cnf(c_956,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_935,c_690])).

cnf(c_957,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_934,c_875,c_956])).

cnf(c_958,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_932,c_957])).

cnf(c_1584,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_2,c_958])).

cnf(c_1647,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1584,c_958])).

cnf(c_349,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_3976,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_1647,c_349])).

cnf(c_4042,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_3976,c_349])).

cnf(c_6727,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_6716,c_4042])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_80,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_9,c_4,c_0])).

cnf(c_222,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_80,c_3])).

cnf(c_618,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_577,c_222])).

cnf(c_16539,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6727,c_618])).

cnf(c_1821,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1647,c_0])).

cnf(c_3971,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_577,c_349])).

cnf(c_3973,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_875,c_349])).

cnf(c_228,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_1159,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_750,c_228])).

cnf(c_1194,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_1159,c_690,c_956,c_958])).

cnf(c_1809,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_3,c_1647])).

cnf(c_1833,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X2)),X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1647,c_227])).

cnf(c_1849,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_1809,c_1833])).

cnf(c_4045,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_3973,c_1194,c_1849])).

cnf(c_4047,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_3971,c_4045])).

cnf(c_16540,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_16539,c_1821,c_4047])).

cnf(c_937,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_875,c_620])).

cnf(c_954,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_937,c_750])).

cnf(c_3640,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_1821,c_954])).

cnf(c_3741,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_3640,c_954])).

cnf(c_429,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_432,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_429,c_4])).

cnf(c_433,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_432,c_349])).

cnf(c_7365,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_433])).

cnf(c_16541,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_16540,c_875,c_3741,c_7365])).

cnf(c_83,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_615,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_84,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_318,plain,
    ( X0 != X1
    | X0 = k2_xboole_0(sK0,sK1)
    | k2_xboole_0(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_448,plain,
    ( X0 != k2_xboole_0(sK1,sK0)
    | X0 = k2_xboole_0(sK0,sK1)
    | k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_485,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK1,sK0)
    | k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1)
    | k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_240,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16541,c_615,c_485,c_240])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:04:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.85/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.98  
% 3.85/0.98  ------  iProver source info
% 3.85/0.98  
% 3.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.98  git: non_committed_changes: false
% 3.85/0.98  git: last_make_outside_of_git: false
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options
% 3.85/0.98  
% 3.85/0.98  --out_options                           all
% 3.85/0.98  --tptp_safe_out                         true
% 3.85/0.98  --problem_path                          ""
% 3.85/0.98  --include_path                          ""
% 3.85/0.98  --clausifier                            res/vclausify_rel
% 3.85/0.98  --clausifier_options                    ""
% 3.85/0.98  --stdin                                 false
% 3.85/0.98  --stats_out                             all
% 3.85/0.98  
% 3.85/0.98  ------ General Options
% 3.85/0.98  
% 3.85/0.98  --fof                                   false
% 3.85/0.98  --time_out_real                         305.
% 3.85/0.98  --time_out_virtual                      -1.
% 3.85/0.98  --symbol_type_check                     false
% 3.85/0.98  --clausify_out                          false
% 3.85/0.98  --sig_cnt_out                           false
% 3.85/0.98  --trig_cnt_out                          false
% 3.85/0.98  --trig_cnt_out_tolerance                1.
% 3.85/0.98  --trig_cnt_out_sk_spl                   false
% 3.85/0.98  --abstr_cl_out                          false
% 3.85/0.98  
% 3.85/0.98  ------ Global Options
% 3.85/0.98  
% 3.85/0.98  --schedule                              default
% 3.85/0.98  --add_important_lit                     false
% 3.85/0.98  --prop_solver_per_cl                    1000
% 3.85/0.98  --min_unsat_core                        false
% 3.85/0.98  --soft_assumptions                      false
% 3.85/0.98  --soft_lemma_size                       3
% 3.85/0.98  --prop_impl_unit_size                   0
% 3.85/0.98  --prop_impl_unit                        []
% 3.85/0.98  --share_sel_clauses                     true
% 3.85/0.98  --reset_solvers                         false
% 3.85/0.98  --bc_imp_inh                            [conj_cone]
% 3.85/0.98  --conj_cone_tolerance                   3.
% 3.85/0.98  --extra_neg_conj                        none
% 3.85/0.98  --large_theory_mode                     true
% 3.85/0.98  --prolific_symb_bound                   200
% 3.85/0.98  --lt_threshold                          2000
% 3.85/0.98  --clause_weak_htbl                      true
% 3.85/0.98  --gc_record_bc_elim                     false
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing Options
% 3.85/0.98  
% 3.85/0.98  --preprocessing_flag                    true
% 3.85/0.98  --time_out_prep_mult                    0.1
% 3.85/0.98  --splitting_mode                        input
% 3.85/0.98  --splitting_grd                         true
% 3.85/0.98  --splitting_cvd                         false
% 3.85/0.98  --splitting_cvd_svl                     false
% 3.85/0.98  --splitting_nvd                         32
% 3.85/0.98  --sub_typing                            true
% 3.85/0.98  --prep_gs_sim                           true
% 3.85/0.98  --prep_unflatten                        true
% 3.85/0.98  --prep_res_sim                          true
% 3.85/0.98  --prep_upred                            true
% 3.85/0.98  --prep_sem_filter                       exhaustive
% 3.85/0.98  --prep_sem_filter_out                   false
% 3.85/0.98  --pred_elim                             true
% 3.85/0.98  --res_sim_input                         true
% 3.85/0.98  --eq_ax_congr_red                       true
% 3.85/0.98  --pure_diseq_elim                       true
% 3.85/0.98  --brand_transform                       false
% 3.85/0.98  --non_eq_to_eq                          false
% 3.85/0.98  --prep_def_merge                        true
% 3.85/0.98  --prep_def_merge_prop_impl              false
% 3.85/0.98  --prep_def_merge_mbd                    true
% 3.85/0.98  --prep_def_merge_tr_red                 false
% 3.85/0.98  --prep_def_merge_tr_cl                  false
% 3.85/0.98  --smt_preprocessing                     true
% 3.85/0.98  --smt_ac_axioms                         fast
% 3.85/0.98  --preprocessed_out                      false
% 3.85/0.98  --preprocessed_stats                    false
% 3.85/0.98  
% 3.85/0.98  ------ Abstraction refinement Options
% 3.85/0.98  
% 3.85/0.98  --abstr_ref                             []
% 3.85/0.98  --abstr_ref_prep                        false
% 3.85/0.98  --abstr_ref_until_sat                   false
% 3.85/0.98  --abstr_ref_sig_restrict                funpre
% 3.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.98  --abstr_ref_under                       []
% 3.85/0.98  
% 3.85/0.98  ------ SAT Options
% 3.85/0.98  
% 3.85/0.98  --sat_mode                              false
% 3.85/0.98  --sat_fm_restart_options                ""
% 3.85/0.98  --sat_gr_def                            false
% 3.85/0.98  --sat_epr_types                         true
% 3.85/0.98  --sat_non_cyclic_types                  false
% 3.85/0.98  --sat_finite_models                     false
% 3.85/0.98  --sat_fm_lemmas                         false
% 3.85/0.98  --sat_fm_prep                           false
% 3.85/0.98  --sat_fm_uc_incr                        true
% 3.85/0.98  --sat_out_model                         small
% 3.85/0.98  --sat_out_clauses                       false
% 3.85/0.98  
% 3.85/0.98  ------ QBF Options
% 3.85/0.98  
% 3.85/0.98  --qbf_mode                              false
% 3.85/0.98  --qbf_elim_univ                         false
% 3.85/0.98  --qbf_dom_inst                          none
% 3.85/0.98  --qbf_dom_pre_inst                      false
% 3.85/0.98  --qbf_sk_in                             false
% 3.85/0.98  --qbf_pred_elim                         true
% 3.85/0.98  --qbf_split                             512
% 3.85/0.98  
% 3.85/0.98  ------ BMC1 Options
% 3.85/0.98  
% 3.85/0.98  --bmc1_incremental                      false
% 3.85/0.98  --bmc1_axioms                           reachable_all
% 3.85/0.98  --bmc1_min_bound                        0
% 3.85/0.98  --bmc1_max_bound                        -1
% 3.85/0.98  --bmc1_max_bound_default                -1
% 3.85/0.98  --bmc1_symbol_reachability              true
% 3.85/0.98  --bmc1_property_lemmas                  false
% 3.85/0.98  --bmc1_k_induction                      false
% 3.85/0.98  --bmc1_non_equiv_states                 false
% 3.85/0.98  --bmc1_deadlock                         false
% 3.85/0.98  --bmc1_ucm                              false
% 3.85/0.98  --bmc1_add_unsat_core                   none
% 3.85/0.98  --bmc1_unsat_core_children              false
% 3.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.98  --bmc1_out_stat                         full
% 3.85/0.98  --bmc1_ground_init                      false
% 3.85/0.98  --bmc1_pre_inst_next_state              false
% 3.85/0.98  --bmc1_pre_inst_state                   false
% 3.85/0.98  --bmc1_pre_inst_reach_state             false
% 3.85/0.98  --bmc1_out_unsat_core                   false
% 3.85/0.98  --bmc1_aig_witness_out                  false
% 3.85/0.98  --bmc1_verbose                          false
% 3.85/0.98  --bmc1_dump_clauses_tptp                false
% 3.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.98  --bmc1_dump_file                        -
% 3.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.98  --bmc1_ucm_extend_mode                  1
% 3.85/0.98  --bmc1_ucm_init_mode                    2
% 3.85/0.98  --bmc1_ucm_cone_mode                    none
% 3.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.98  --bmc1_ucm_relax_model                  4
% 3.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.98  --bmc1_ucm_layered_model                none
% 3.85/0.98  --bmc1_ucm_max_lemma_size               10
% 3.85/0.98  
% 3.85/0.98  ------ AIG Options
% 3.85/0.98  
% 3.85/0.98  --aig_mode                              false
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation Options
% 3.85/0.98  
% 3.85/0.98  --instantiation_flag                    true
% 3.85/0.98  --inst_sos_flag                         true
% 3.85/0.98  --inst_sos_phase                        true
% 3.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel_side                     num_symb
% 3.85/0.98  --inst_solver_per_active                1400
% 3.85/0.98  --inst_solver_calls_frac                1.
% 3.85/0.98  --inst_passive_queue_type               priority_queues
% 3.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.98  --inst_passive_queues_freq              [25;2]
% 3.85/0.98  --inst_dismatching                      true
% 3.85/0.98  --inst_eager_unprocessed_to_passive     true
% 3.85/0.98  --inst_prop_sim_given                   true
% 3.85/0.98  --inst_prop_sim_new                     false
% 3.85/0.98  --inst_subs_new                         false
% 3.85/0.98  --inst_eq_res_simp                      false
% 3.85/0.98  --inst_subs_given                       false
% 3.85/0.98  --inst_orphan_elimination               true
% 3.85/0.98  --inst_learning_loop_flag               true
% 3.85/0.98  --inst_learning_start                   3000
% 3.85/0.98  --inst_learning_factor                  2
% 3.85/0.98  --inst_start_prop_sim_after_learn       3
% 3.85/0.98  --inst_sel_renew                        solver
% 3.85/0.98  --inst_lit_activity_flag                true
% 3.85/0.98  --inst_restr_to_given                   false
% 3.85/0.98  --inst_activity_threshold               500
% 3.85/0.98  --inst_out_proof                        true
% 3.85/0.98  
% 3.85/0.98  ------ Resolution Options
% 3.85/0.98  
% 3.85/0.98  --resolution_flag                       true
% 3.85/0.98  --res_lit_sel                           adaptive
% 3.85/0.98  --res_lit_sel_side                      none
% 3.85/0.98  --res_ordering                          kbo
% 3.85/0.98  --res_to_prop_solver                    active
% 3.85/0.98  --res_prop_simpl_new                    false
% 3.85/0.98  --res_prop_simpl_given                  true
% 3.85/0.98  --res_passive_queue_type                priority_queues
% 3.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.98  --res_passive_queues_freq               [15;5]
% 3.85/0.98  --res_forward_subs                      full
% 3.85/0.98  --res_backward_subs                     full
% 3.85/0.98  --res_forward_subs_resolution           true
% 3.85/0.98  --res_backward_subs_resolution          true
% 3.85/0.98  --res_orphan_elimination                true
% 3.85/0.98  --res_time_limit                        2.
% 3.85/0.98  --res_out_proof                         true
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Options
% 3.85/0.98  
% 3.85/0.98  --superposition_flag                    true
% 3.85/0.98  --sup_passive_queue_type                priority_queues
% 3.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.98  --demod_completeness_check              fast
% 3.85/0.98  --demod_use_ground                      true
% 3.85/0.98  --sup_to_prop_solver                    passive
% 3.85/0.98  --sup_prop_simpl_new                    true
% 3.85/0.98  --sup_prop_simpl_given                  true
% 3.85/0.98  --sup_fun_splitting                     true
% 3.85/0.98  --sup_smt_interval                      50000
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Simplification Setup
% 3.85/0.98  
% 3.85/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_immed_triv                        [TrivRules]
% 3.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_bw_main                     []
% 3.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_input_bw                          []
% 3.85/0.98  
% 3.85/0.98  ------ Combination Options
% 3.85/0.98  
% 3.85/0.98  --comb_res_mult                         3
% 3.85/0.98  --comb_sup_mult                         2
% 3.85/0.98  --comb_inst_mult                        10
% 3.85/0.98  
% 3.85/0.98  ------ Debug Options
% 3.85/0.98  
% 3.85/0.98  --dbg_backtrace                         false
% 3.85/0.98  --dbg_dump_prop_clauses                 false
% 3.85/0.98  --dbg_dump_prop_clauses_file            -
% 3.85/0.98  --dbg_out_stat                          false
% 3.85/0.98  ------ Parsing...
% 3.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  ------ Proving...
% 3.85/0.98  ------ Problem Properties 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  clauses                                 10
% 3.85/0.98  conjectures                             1
% 3.85/0.98  EPR                                     1
% 3.85/0.98  Horn                                    10
% 3.85/0.98  unary                                   7
% 3.85/0.98  binary                                  3
% 3.85/0.98  lits                                    13
% 3.85/0.98  lits eq                                 8
% 3.85/0.98  fd_pure                                 0
% 3.85/0.98  fd_pseudo                               0
% 3.85/0.98  fd_cond                                 0
% 3.85/0.98  fd_pseudo_cond                          0
% 3.85/0.98  AC symbols                              1
% 3.85/0.98  
% 3.85/0.98  ------ Schedule dynamic 5 is on 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  Current options:
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  ------ Input Options
% 3.85/0.98  
% 3.85/0.98  --out_options                           all
% 3.85/0.98  --tptp_safe_out                         true
% 3.85/0.98  --problem_path                          ""
% 3.85/0.98  --include_path                          ""
% 3.85/0.98  --clausifier                            res/vclausify_rel
% 3.85/0.98  --clausifier_options                    ""
% 3.85/0.98  --stdin                                 false
% 3.85/0.98  --stats_out                             all
% 3.85/0.98  
% 3.85/0.98  ------ General Options
% 3.85/0.98  
% 3.85/0.98  --fof                                   false
% 3.85/0.98  --time_out_real                         305.
% 3.85/0.98  --time_out_virtual                      -1.
% 3.85/0.98  --symbol_type_check                     false
% 3.85/0.98  --clausify_out                          false
% 3.85/0.98  --sig_cnt_out                           false
% 3.85/0.98  --trig_cnt_out                          false
% 3.85/0.98  --trig_cnt_out_tolerance                1.
% 3.85/0.98  --trig_cnt_out_sk_spl                   false
% 3.85/0.98  --abstr_cl_out                          false
% 3.85/0.98  
% 3.85/0.98  ------ Global Options
% 3.85/0.98  
% 3.85/0.98  --schedule                              default
% 3.85/0.98  --add_important_lit                     false
% 3.85/0.98  --prop_solver_per_cl                    1000
% 3.85/0.98  --min_unsat_core                        false
% 3.85/0.98  --soft_assumptions                      false
% 3.85/0.98  --soft_lemma_size                       3
% 3.85/0.98  --prop_impl_unit_size                   0
% 3.85/0.98  --prop_impl_unit                        []
% 3.85/0.98  --share_sel_clauses                     true
% 3.85/0.98  --reset_solvers                         false
% 3.85/0.98  --bc_imp_inh                            [conj_cone]
% 3.85/0.98  --conj_cone_tolerance                   3.
% 3.85/0.98  --extra_neg_conj                        none
% 3.85/0.98  --large_theory_mode                     true
% 3.85/0.98  --prolific_symb_bound                   200
% 3.85/0.98  --lt_threshold                          2000
% 3.85/0.98  --clause_weak_htbl                      true
% 3.85/0.98  --gc_record_bc_elim                     false
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing Options
% 3.85/0.98  
% 3.85/0.98  --preprocessing_flag                    true
% 3.85/0.98  --time_out_prep_mult                    0.1
% 3.85/0.98  --splitting_mode                        input
% 3.85/0.98  --splitting_grd                         true
% 3.85/0.98  --splitting_cvd                         false
% 3.85/0.98  --splitting_cvd_svl                     false
% 3.85/0.98  --splitting_nvd                         32
% 3.85/0.98  --sub_typing                            true
% 3.85/0.98  --prep_gs_sim                           true
% 3.85/0.98  --prep_unflatten                        true
% 3.85/0.98  --prep_res_sim                          true
% 3.85/0.98  --prep_upred                            true
% 3.85/0.98  --prep_sem_filter                       exhaustive
% 3.85/0.98  --prep_sem_filter_out                   false
% 3.85/0.98  --pred_elim                             true
% 3.85/0.98  --res_sim_input                         true
% 3.85/0.98  --eq_ax_congr_red                       true
% 3.85/0.98  --pure_diseq_elim                       true
% 3.85/0.98  --brand_transform                       false
% 3.85/0.98  --non_eq_to_eq                          false
% 3.85/0.98  --prep_def_merge                        true
% 3.85/0.98  --prep_def_merge_prop_impl              false
% 3.85/0.98  --prep_def_merge_mbd                    true
% 3.85/0.98  --prep_def_merge_tr_red                 false
% 3.85/0.98  --prep_def_merge_tr_cl                  false
% 3.85/0.98  --smt_preprocessing                     true
% 3.85/0.98  --smt_ac_axioms                         fast
% 3.85/0.98  --preprocessed_out                      false
% 3.85/0.98  --preprocessed_stats                    false
% 3.85/0.98  
% 3.85/0.98  ------ Abstraction refinement Options
% 3.85/0.98  
% 3.85/0.98  --abstr_ref                             []
% 3.85/0.98  --abstr_ref_prep                        false
% 3.85/0.98  --abstr_ref_until_sat                   false
% 3.85/0.98  --abstr_ref_sig_restrict                funpre
% 3.85/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/0.98  --abstr_ref_under                       []
% 3.85/0.98  
% 3.85/0.98  ------ SAT Options
% 3.85/0.98  
% 3.85/0.98  --sat_mode                              false
% 3.85/0.98  --sat_fm_restart_options                ""
% 3.85/0.98  --sat_gr_def                            false
% 3.85/0.98  --sat_epr_types                         true
% 3.85/0.98  --sat_non_cyclic_types                  false
% 3.85/0.98  --sat_finite_models                     false
% 3.85/0.98  --sat_fm_lemmas                         false
% 3.85/0.98  --sat_fm_prep                           false
% 3.85/0.98  --sat_fm_uc_incr                        true
% 3.85/0.98  --sat_out_model                         small
% 3.85/0.98  --sat_out_clauses                       false
% 3.85/0.98  
% 3.85/0.98  ------ QBF Options
% 3.85/0.98  
% 3.85/0.98  --qbf_mode                              false
% 3.85/0.98  --qbf_elim_univ                         false
% 3.85/0.98  --qbf_dom_inst                          none
% 3.85/0.98  --qbf_dom_pre_inst                      false
% 3.85/0.98  --qbf_sk_in                             false
% 3.85/0.98  --qbf_pred_elim                         true
% 3.85/0.98  --qbf_split                             512
% 3.85/0.98  
% 3.85/0.98  ------ BMC1 Options
% 3.85/0.98  
% 3.85/0.98  --bmc1_incremental                      false
% 3.85/0.98  --bmc1_axioms                           reachable_all
% 3.85/0.98  --bmc1_min_bound                        0
% 3.85/0.98  --bmc1_max_bound                        -1
% 3.85/0.98  --bmc1_max_bound_default                -1
% 3.85/0.98  --bmc1_symbol_reachability              true
% 3.85/0.98  --bmc1_property_lemmas                  false
% 3.85/0.98  --bmc1_k_induction                      false
% 3.85/0.98  --bmc1_non_equiv_states                 false
% 3.85/0.98  --bmc1_deadlock                         false
% 3.85/0.98  --bmc1_ucm                              false
% 3.85/0.98  --bmc1_add_unsat_core                   none
% 3.85/0.98  --bmc1_unsat_core_children              false
% 3.85/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/0.98  --bmc1_out_stat                         full
% 3.85/0.98  --bmc1_ground_init                      false
% 3.85/0.98  --bmc1_pre_inst_next_state              false
% 3.85/0.98  --bmc1_pre_inst_state                   false
% 3.85/0.98  --bmc1_pre_inst_reach_state             false
% 3.85/0.98  --bmc1_out_unsat_core                   false
% 3.85/0.98  --bmc1_aig_witness_out                  false
% 3.85/0.98  --bmc1_verbose                          false
% 3.85/0.98  --bmc1_dump_clauses_tptp                false
% 3.85/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.85/0.98  --bmc1_dump_file                        -
% 3.85/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.85/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.85/0.98  --bmc1_ucm_extend_mode                  1
% 3.85/0.98  --bmc1_ucm_init_mode                    2
% 3.85/0.98  --bmc1_ucm_cone_mode                    none
% 3.85/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.85/0.98  --bmc1_ucm_relax_model                  4
% 3.85/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.85/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/0.98  --bmc1_ucm_layered_model                none
% 3.85/0.98  --bmc1_ucm_max_lemma_size               10
% 3.85/0.98  
% 3.85/0.98  ------ AIG Options
% 3.85/0.98  
% 3.85/0.98  --aig_mode                              false
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation Options
% 3.85/0.98  
% 3.85/0.98  --instantiation_flag                    true
% 3.85/0.98  --inst_sos_flag                         true
% 3.85/0.98  --inst_sos_phase                        true
% 3.85/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/0.98  --inst_lit_sel_side                     none
% 3.85/0.98  --inst_solver_per_active                1400
% 3.85/0.98  --inst_solver_calls_frac                1.
% 3.85/0.98  --inst_passive_queue_type               priority_queues
% 3.85/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/0.98  --inst_passive_queues_freq              [25;2]
% 3.85/0.98  --inst_dismatching                      true
% 3.85/0.98  --inst_eager_unprocessed_to_passive     true
% 3.85/0.98  --inst_prop_sim_given                   true
% 3.85/0.98  --inst_prop_sim_new                     false
% 3.85/0.98  --inst_subs_new                         false
% 3.85/0.98  --inst_eq_res_simp                      false
% 3.85/0.98  --inst_subs_given                       false
% 3.85/0.98  --inst_orphan_elimination               true
% 3.85/0.98  --inst_learning_loop_flag               true
% 3.85/0.98  --inst_learning_start                   3000
% 3.85/0.98  --inst_learning_factor                  2
% 3.85/0.98  --inst_start_prop_sim_after_learn       3
% 3.85/0.98  --inst_sel_renew                        solver
% 3.85/0.98  --inst_lit_activity_flag                true
% 3.85/0.98  --inst_restr_to_given                   false
% 3.85/0.98  --inst_activity_threshold               500
% 3.85/0.98  --inst_out_proof                        true
% 3.85/0.98  
% 3.85/0.98  ------ Resolution Options
% 3.85/0.98  
% 3.85/0.98  --resolution_flag                       false
% 3.85/0.98  --res_lit_sel                           adaptive
% 3.85/0.98  --res_lit_sel_side                      none
% 3.85/0.98  --res_ordering                          kbo
% 3.85/0.98  --res_to_prop_solver                    active
% 3.85/0.98  --res_prop_simpl_new                    false
% 3.85/0.98  --res_prop_simpl_given                  true
% 3.85/0.98  --res_passive_queue_type                priority_queues
% 3.85/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/0.98  --res_passive_queues_freq               [15;5]
% 3.85/0.98  --res_forward_subs                      full
% 3.85/0.98  --res_backward_subs                     full
% 3.85/0.98  --res_forward_subs_resolution           true
% 3.85/0.98  --res_backward_subs_resolution          true
% 3.85/0.98  --res_orphan_elimination                true
% 3.85/0.98  --res_time_limit                        2.
% 3.85/0.98  --res_out_proof                         true
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Options
% 3.85/0.98  
% 3.85/0.98  --superposition_flag                    true
% 3.85/0.98  --sup_passive_queue_type                priority_queues
% 3.85/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.85/0.98  --demod_completeness_check              fast
% 3.85/0.98  --demod_use_ground                      true
% 3.85/0.98  --sup_to_prop_solver                    passive
% 3.85/0.98  --sup_prop_simpl_new                    true
% 3.85/0.98  --sup_prop_simpl_given                  true
% 3.85/0.98  --sup_fun_splitting                     true
% 3.85/0.98  --sup_smt_interval                      50000
% 3.85/0.98  
% 3.85/0.98  ------ Superposition Simplification Setup
% 3.85/0.98  
% 3.85/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.85/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.85/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.85/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_immed_triv                        [TrivRules]
% 3.85/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_immed_bw_main                     []
% 3.85/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.85/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/0.98  --sup_input_bw                          []
% 3.85/0.98  
% 3.85/0.98  ------ Combination Options
% 3.85/0.98  
% 3.85/0.98  --comb_res_mult                         3
% 3.85/0.98  --comb_sup_mult                         2
% 3.85/0.98  --comb_inst_mult                        10
% 3.85/0.98  
% 3.85/0.98  ------ Debug Options
% 3.85/0.98  
% 3.85/0.98  --dbg_backtrace                         false
% 3.85/0.98  --dbg_dump_prop_clauses                 false
% 3.85/0.98  --dbg_dump_prop_clauses_file            -
% 3.85/0.98  --dbg_out_stat                          false
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS status Theorem for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  fof(f9,axiom,(
% 3.85/0.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f26,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f9])).
% 3.85/0.98  
% 3.85/0.98  fof(f3,axiom,(
% 3.85/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f13,plain,(
% 3.85/0.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.85/0.98    inference(ennf_transformation,[],[f3])).
% 3.85/0.98  
% 3.85/0.98  fof(f20,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f13])).
% 3.85/0.98  
% 3.85/0.98  fof(f10,axiom,(
% 3.85/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f15,plain,(
% 3.85/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.85/0.98    inference(nnf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f27,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f5,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f22,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f5])).
% 3.85/0.98  
% 3.85/0.98  fof(f4,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f21,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f4])).
% 3.85/0.98  
% 3.85/0.98  fof(f1,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f18,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f1])).
% 3.85/0.98  
% 3.85/0.98  fof(f8,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f25,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.85/0.98    inference(cnf_transformation,[],[f8])).
% 3.85/0.98  
% 3.85/0.98  fof(f6,axiom,(
% 3.85/0.98    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f23,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f6])).
% 3.85/0.98  
% 3.85/0.98  fof(f30,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 3.85/0.98    inference(definition_unfolding,[],[f25,f23])).
% 3.85/0.98  
% 3.85/0.98  fof(f7,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f24,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f7])).
% 3.85/0.98  
% 3.85/0.98  fof(f11,conjecture,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f12,negated_conjecture,(
% 3.85/0.98    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.85/0.98    inference(negated_conjecture,[],[f11])).
% 3.85/0.98  
% 3.85/0.98  fof(f14,plain,(
% 3.85/0.98    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.85/0.98    inference(ennf_transformation,[],[f12])).
% 3.85/0.98  
% 3.85/0.98  fof(f16,plain,(
% 3.85/0.98    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f17,plain,(
% 3.85/0.98    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 3.85/0.98  
% 3.85/0.98  fof(f29,plain,(
% 3.85/0.98    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 3.85/0.98    inference(cnf_transformation,[],[f17])).
% 3.85/0.98  
% 3.85/0.98  fof(f2,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f19,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f2])).
% 3.85/0.98  
% 3.85/0.98  fof(f31,plain,(
% 3.85/0.98    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 3.85/0.98    inference(definition_unfolding,[],[f29,f19,f19,f23])).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6,plain,
% 3.85/0.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f26]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_220,plain,
% 3.85/0.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1,plain,
% 3.85/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f20]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_221,plain,
% 3.85/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 3.85/0.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6132,plain,
% 3.85/0.98      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_220,c_221]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_8,plain,
% 3.85/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_218,plain,
% 3.85/0.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6549,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_6132,c_218]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3,plain,
% 3.85/0.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f22]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6716,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_6549,c_3]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f21]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_0,plain,
% 3.85/0.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f18]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_5,plain,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.85/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f24]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_81,plain,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.85/0.98      inference(theory_normalisation,[status(thm)],[c_5,c_4,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_496,plain,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_81,c_2]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_512,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_496,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_568,plain,
% 3.85/0.98      ( k2_xboole_0(X0,X0) = X0 ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_512,c_2]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_577,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_568,c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_620,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_0,c_577]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_681,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_577,c_620]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_692,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_681,c_568]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_750,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_0,c_692]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_227,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_875,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_568,c_227]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_932,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_750,c_875]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_934,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_875,c_692]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_935,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_875,c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_684,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_620,c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_690,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_684,c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_956,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_935,c_690]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_957,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_934,c_875,c_956]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_958,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_932,c_957]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1584,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_2,c_958]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1647,plain,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_1584,c_958]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_349,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3976,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1647,c_349]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4042,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_3976,c_349]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6727,plain,
% 3.85/0.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_6716,c_4042]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9,negated_conjecture,
% 3.85/0.98      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 3.85/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_80,negated_conjecture,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 3.85/0.98      inference(theory_normalisation,[status(thm)],[c_9,c_4,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_222,plain,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_80,c_3]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_618,plain,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_577,c_222]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_16539,plain,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_6727,c_618]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1821,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1647,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3971,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_577,c_349]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3973,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_875,c_349]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_228,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1159,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_750,c_228]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1194,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_1159,c_690,c_956,c_958]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1809,plain,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_3,c_1647]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1833,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X2)),X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1647,c_227]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1849,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_1809,c_1833]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4045,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_3973,c_1194,c_1849]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4047,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_3971,c_4045]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_16540,plain,
% 3.85/0.98      ( k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,sK1))) != k2_xboole_0(sK0,sK1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_16539,c_1821,c_4047]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_937,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_875,c_620]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_954,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_937,c_750]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3640,plain,
% 3.85/0.98      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1821,c_954]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3741,plain,
% 3.85/0.98      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_3640,c_954]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_429,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_432,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(light_normalisation,[status(thm)],[c_429,c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_433,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_432,c_349]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7365,plain,
% 3.85/0.98      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_0,c_433]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_16541,plain,
% 3.85/0.98      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 3.85/0.98      inference(demodulation,[status(thm)],[c_16540,c_875,c_3741,c_7365]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_83,plain,( X0 = X0 ),theory(equality) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_615,plain,
% 3.85/0.98      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,sK0) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_83]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_84,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_318,plain,
% 3.85/0.98      ( X0 != X1
% 3.85/0.98      | X0 = k2_xboole_0(sK0,sK1)
% 3.85/0.98      | k2_xboole_0(sK0,sK1) != X1 ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_84]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_448,plain,
% 3.85/0.98      ( X0 != k2_xboole_0(sK1,sK0)
% 3.85/0.98      | X0 = k2_xboole_0(sK0,sK1)
% 3.85/0.98      | k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_318]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_485,plain,
% 3.85/0.98      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK1,sK0)
% 3.85/0.98      | k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1)
% 3.85/0.98      | k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_448]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_240,plain,
% 3.85/0.98      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK0) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(contradiction,plain,
% 3.85/0.98      ( $false ),
% 3.85/0.98      inference(minisat,[status(thm)],[c_16541,c_615,c_485,c_240]) ).
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  ------                               Statistics
% 3.85/0.98  
% 3.85/0.98  ------ General
% 3.85/0.98  
% 3.85/0.98  abstr_ref_over_cycles:                  0
% 3.85/0.98  abstr_ref_under_cycles:                 0
% 3.85/0.98  gc_basic_clause_elim:                   0
% 3.85/0.98  forced_gc_time:                         0
% 3.85/0.98  parsing_time:                           0.007
% 3.85/0.98  unif_index_cands_time:                  0.
% 3.85/0.98  unif_index_add_time:                    0.
% 3.85/0.98  orderings_time:                         0.
% 3.85/0.98  out_proof_time:                         0.007
% 3.85/0.98  total_time:                             0.49
% 3.85/0.98  num_of_symbols:                         36
% 3.85/0.98  num_of_terms:                           21317
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing
% 3.85/0.98  
% 3.85/0.98  num_of_splits:                          0
% 3.85/0.98  num_of_split_atoms:                     0
% 3.85/0.98  num_of_reused_defs:                     0
% 3.85/0.98  num_eq_ax_congr_red:                    2
% 3.85/0.98  num_of_sem_filtered_clauses:            1
% 3.85/0.98  num_of_subtypes:                        0
% 3.85/0.98  monotx_restored_types:                  0
% 3.85/0.98  sat_num_of_epr_types:                   0
% 3.85/0.98  sat_num_of_non_cyclic_types:            0
% 3.85/0.98  sat_guarded_non_collapsed_types:        0
% 3.85/0.98  num_pure_diseq_elim:                    0
% 3.85/0.98  simp_replaced_by:                       0
% 3.85/0.98  res_preprocessed:                       41
% 3.85/0.98  prep_upred:                             0
% 3.85/0.98  prep_unflattend:                        0
% 3.85/0.98  smt_new_axioms:                         0
% 3.85/0.98  pred_elim_cands:                        1
% 3.85/0.98  pred_elim:                              0
% 3.85/0.98  pred_elim_cl:                           0
% 3.85/0.98  pred_elim_cycles:                       1
% 3.85/0.98  merged_defs:                            6
% 3.85/0.98  merged_defs_ncl:                        0
% 3.85/0.98  bin_hyper_res:                          6
% 3.85/0.98  prep_cycles:                            3
% 3.85/0.98  pred_elim_time:                         0.
% 3.85/0.98  splitting_time:                         0.
% 3.85/0.98  sem_filter_time:                        0.
% 3.85/0.98  monotx_time:                            0.
% 3.85/0.98  subtype_inf_time:                       0.
% 3.85/0.98  
% 3.85/0.98  ------ Problem properties
% 3.85/0.98  
% 3.85/0.98  clauses:                                10
% 3.85/0.98  conjectures:                            1
% 3.85/0.98  epr:                                    1
% 3.85/0.98  horn:                                   10
% 3.85/0.98  ground:                                 1
% 3.85/0.98  unary:                                  7
% 3.85/0.98  binary:                                 3
% 3.85/0.98  lits:                                   13
% 3.85/0.98  lits_eq:                                8
% 3.85/0.98  fd_pure:                                0
% 3.85/0.98  fd_pseudo:                              0
% 3.85/0.98  fd_cond:                                0
% 3.85/0.98  fd_pseudo_cond:                         0
% 3.85/0.98  ac_symbols:                             1
% 3.85/0.98  
% 3.85/0.98  ------ Propositional Solver
% 3.85/0.98  
% 3.85/0.98  prop_solver_calls:                      29
% 3.85/0.98  prop_fast_solver_calls:                 254
% 3.85/0.98  smt_solver_calls:                       0
% 3.85/0.98  smt_fast_solver_calls:                  0
% 3.85/0.98  prop_num_of_clauses:                    4062
% 3.85/0.98  prop_preprocess_simplified:             5356
% 3.85/0.98  prop_fo_subsumed:                       0
% 3.85/0.98  prop_solver_time:                       0.
% 3.85/0.98  smt_solver_time:                        0.
% 3.85/0.98  smt_fast_solver_time:                   0.
% 3.85/0.98  prop_fast_solver_time:                  0.
% 3.85/0.98  prop_unsat_core_time:                   0.
% 3.85/0.98  
% 3.85/0.98  ------ QBF
% 3.85/0.98  
% 3.85/0.98  qbf_q_res:                              0
% 3.85/0.98  qbf_num_tautologies:                    0
% 3.85/0.98  qbf_prep_cycles:                        0
% 3.85/0.98  
% 3.85/0.98  ------ BMC1
% 3.85/0.98  
% 3.85/0.98  bmc1_current_bound:                     -1
% 3.85/0.98  bmc1_last_solved_bound:                 -1
% 3.85/0.98  bmc1_unsat_core_size:                   -1
% 3.85/0.98  bmc1_unsat_core_parents_size:           -1
% 3.85/0.98  bmc1_merge_next_fun:                    0
% 3.85/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.85/0.98  
% 3.85/0.98  ------ Instantiation
% 3.85/0.98  
% 3.85/0.98  inst_num_of_clauses:                    1184
% 3.85/0.98  inst_num_in_passive:                    216
% 3.85/0.98  inst_num_in_active:                     472
% 3.85/0.98  inst_num_in_unprocessed:                499
% 3.85/0.98  inst_num_of_loops:                      530
% 3.85/0.98  inst_num_of_learning_restarts:          0
% 3.85/0.98  inst_num_moves_active_passive:          52
% 3.85/0.98  inst_lit_activity:                      0
% 3.85/0.98  inst_lit_activity_moves:                0
% 3.85/0.98  inst_num_tautologies:                   0
% 3.85/0.98  inst_num_prop_implied:                  0
% 3.85/0.98  inst_num_existing_simplified:           0
% 3.85/0.98  inst_num_eq_res_simplified:             0
% 3.85/0.98  inst_num_child_elim:                    0
% 3.85/0.98  inst_num_of_dismatching_blockings:      785
% 3.85/0.98  inst_num_of_non_proper_insts:           1721
% 3.85/0.98  inst_num_of_duplicates:                 0
% 3.85/0.98  inst_inst_num_from_inst_to_res:         0
% 3.85/0.98  inst_dismatching_checking_time:         0.
% 3.85/0.98  
% 3.85/0.98  ------ Resolution
% 3.85/0.98  
% 3.85/0.98  res_num_of_clauses:                     0
% 3.85/0.98  res_num_in_passive:                     0
% 3.85/0.98  res_num_in_active:                      0
% 3.85/0.98  res_num_of_loops:                       44
% 3.85/0.98  res_forward_subset_subsumed:            755
% 3.85/0.98  res_backward_subset_subsumed:           12
% 3.85/0.98  res_forward_subsumed:                   0
% 3.85/0.98  res_backward_subsumed:                  0
% 3.85/0.98  res_forward_subsumption_resolution:     0
% 3.85/0.98  res_backward_subsumption_resolution:    0
% 3.85/0.98  res_clause_to_clause_subsumption:       32987
% 3.85/0.98  res_orphan_elimination:                 0
% 3.85/0.98  res_tautology_del:                      246
% 3.85/0.98  res_num_eq_res_simplified:              0
% 3.85/0.98  res_num_sel_changes:                    0
% 3.85/0.98  res_moves_from_active_to_pass:          0
% 3.85/0.98  
% 3.85/0.98  ------ Superposition
% 3.85/0.98  
% 3.85/0.98  sup_time_total:                         0.
% 3.85/0.98  sup_time_generating:                    0.
% 3.85/0.98  sup_time_sim_full:                      0.
% 3.85/0.98  sup_time_sim_immed:                     0.
% 3.85/0.98  
% 3.85/0.98  sup_num_of_clauses:                     1185
% 3.85/0.98  sup_num_in_active:                      96
% 3.85/0.98  sup_num_in_passive:                     1089
% 3.85/0.98  sup_num_of_loops:                       104
% 3.85/0.98  sup_fw_superposition:                   3900
% 3.85/0.98  sup_bw_superposition:                   3146
% 3.85/0.98  sup_immediate_simplified:               2910
% 3.85/0.98  sup_given_eliminated:                   0
% 3.85/0.98  comparisons_done:                       0
% 3.85/0.98  comparisons_avoided:                    0
% 3.85/0.98  
% 3.85/0.98  ------ Simplifications
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  sim_fw_subset_subsumed:                 0
% 3.85/0.98  sim_bw_subset_subsumed:                 0
% 3.85/0.98  sim_fw_subsumed:                        514
% 3.85/0.98  sim_bw_subsumed:                        13
% 3.85/0.98  sim_fw_subsumption_res:                 0
% 3.85/0.98  sim_bw_subsumption_res:                 0
% 3.85/0.98  sim_tautology_del:                      0
% 3.85/0.98  sim_eq_tautology_del:                   338
% 3.85/0.98  sim_eq_res_simp:                        0
% 3.85/0.98  sim_fw_demodulated:                     1855
% 3.85/0.98  sim_bw_demodulated:                     11
% 3.85/0.98  sim_light_normalised:                   848
% 3.85/0.98  sim_joinable_taut:                      88
% 3.85/0.98  sim_joinable_simp:                      0
% 3.85/0.98  sim_ac_normalised:                      0
% 3.85/0.98  sim_smt_subsumption:                    0
% 3.85/0.98  
%------------------------------------------------------------------------------
