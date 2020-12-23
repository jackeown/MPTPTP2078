%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:44 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 474 expanded)
%              Number of clauses        :   58 ( 170 expanded)
%              Number of leaves         :   18 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :  127 ( 544 expanded)
%              Number of equality atoms :   90 ( 437 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f106,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f84,f55])).

fof(f28,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f28])).

fof(f22,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f76,f55])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f31,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f86,f66])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f69,f89])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f32,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_tarski(sK1,sK2) )
      & r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( ~ r1_xboole_0(sK1,sK3)
      | ~ r1_tarski(sK1,sK2) )
    & r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f51])).

fof(f87,plain,(
    r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f108,plain,(
    r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(definition_unfolding,[],[f87,f66])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f20])).

fof(f99,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f74,f66,f66])).

fof(f19,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,(
    ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f73,f55,f55])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f88,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_28,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1489,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_29,c_28])).

cnf(c_21,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1320,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_21,c_1])).

cnf(c_2298,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1489,c_1320])).

cnf(c_2303,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_2298])).

cnf(c_2400,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_2298,c_2303])).

cnf(c_2443,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_2400,c_28])).

cnf(c_14,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_12,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_501,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_14,c_28,c_1,c_12,c_0])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_494,negated_conjecture,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) ),
    inference(theory_normalisation,[status(thm)],[c_32,c_28,c_1,c_12,c_0])).

cnf(c_927,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_935,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_27020,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_927,c_935])).

cnf(c_29446,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)) = k3_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_27020,c_12])).

cnf(c_33554,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_501,c_29446])).

cnf(c_33913,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_33554,c_27020])).

cnf(c_41112,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(sK3,sK2)))) = sK1 ),
    inference(superposition,[status(thm)],[c_2443,c_33913])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1471,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_12])).

cnf(c_2266,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1471])).

cnf(c_19,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_498,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_19,c_28,c_1,c_12,c_0])).

cnf(c_3224,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2266,c_498])).

cnf(c_3277,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3224,c_29])).

cnf(c_3837,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_3277])).

cnf(c_4546,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_3837,c_2266])).

cnf(c_18,plain,
    ( k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4562,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4546,c_18])).

cnf(c_4922,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X1,X2)) = k3_xboole_0(o_0_0_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_4562,c_12])).

cnf(c_1315,plain,
    ( k3_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_18,c_0])).

cnf(c_4946,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X1,X2)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4922,c_1315])).

cnf(c_41465,plain,
    ( k3_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_41112,c_21,c_4946])).

cnf(c_13,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_936,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1589,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_936])).

cnf(c_42587,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_41465,c_1589])).

cnf(c_1050,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_5745,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,X2)))) = k3_xboole_0(X1,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_3837,c_1050])).

cnf(c_5886,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,X2)))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5745,c_18])).

cnf(c_29494,plain,
    ( k3_xboole_0(sK3,sK1) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_27020,c_5886])).

cnf(c_11,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_937,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2309,plain,
    ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2298,c_937])).

cnf(c_5390,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_501,c_2309])).

cnf(c_6198,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(X1,o_0_0_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4562,c_5390])).

cnf(c_6200,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6198,c_21])).

cnf(c_29866,plain,
    ( r1_xboole_0(k5_xboole_0(sK1,o_0_0_xboole_0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_29494,c_6200])).

cnf(c_29980,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_29866,c_21])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,plain,
    ( r1_tarski(sK1,sK2) != iProver_top
    | r1_xboole_0(sK1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42587,c_29980,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:51:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.36/1.54  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/1.54  
% 7.36/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.36/1.54  
% 7.36/1.54  ------  iProver source info
% 7.36/1.54  
% 7.36/1.54  git: date: 2020-06-30 10:37:57 +0100
% 7.36/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.36/1.54  git: non_committed_changes: false
% 7.36/1.54  git: last_make_outside_of_git: false
% 7.36/1.54  
% 7.36/1.54  ------ 
% 7.36/1.54  
% 7.36/1.54  ------ Input Options
% 7.36/1.54  
% 7.36/1.54  --out_options                           all
% 7.36/1.54  --tptp_safe_out                         true
% 7.36/1.54  --problem_path                          ""
% 7.36/1.54  --include_path                          ""
% 7.36/1.54  --clausifier                            res/vclausify_rel
% 7.36/1.54  --clausifier_options                    --mode clausify
% 7.36/1.54  --stdin                                 false
% 7.36/1.54  --stats_out                             all
% 7.36/1.54  
% 7.36/1.54  ------ General Options
% 7.36/1.54  
% 7.36/1.54  --fof                                   false
% 7.36/1.54  --time_out_real                         305.
% 7.36/1.54  --time_out_virtual                      -1.
% 7.36/1.54  --symbol_type_check                     false
% 7.36/1.54  --clausify_out                          false
% 7.36/1.54  --sig_cnt_out                           false
% 7.36/1.54  --trig_cnt_out                          false
% 7.36/1.54  --trig_cnt_out_tolerance                1.
% 7.36/1.54  --trig_cnt_out_sk_spl                   false
% 7.36/1.54  --abstr_cl_out                          false
% 7.36/1.54  
% 7.36/1.54  ------ Global Options
% 7.36/1.54  
% 7.36/1.54  --schedule                              default
% 7.36/1.54  --add_important_lit                     false
% 7.36/1.54  --prop_solver_per_cl                    1000
% 7.36/1.54  --min_unsat_core                        false
% 7.36/1.54  --soft_assumptions                      false
% 7.36/1.54  --soft_lemma_size                       3
% 7.36/1.54  --prop_impl_unit_size                   0
% 7.36/1.54  --prop_impl_unit                        []
% 7.36/1.54  --share_sel_clauses                     true
% 7.36/1.54  --reset_solvers                         false
% 7.36/1.54  --bc_imp_inh                            [conj_cone]
% 7.36/1.54  --conj_cone_tolerance                   3.
% 7.36/1.54  --extra_neg_conj                        none
% 7.36/1.54  --large_theory_mode                     true
% 7.36/1.54  --prolific_symb_bound                   200
% 7.36/1.54  --lt_threshold                          2000
% 7.36/1.54  --clause_weak_htbl                      true
% 7.36/1.54  --gc_record_bc_elim                     false
% 7.36/1.54  
% 7.36/1.54  ------ Preprocessing Options
% 7.36/1.54  
% 7.36/1.54  --preprocessing_flag                    true
% 7.36/1.54  --time_out_prep_mult                    0.1
% 7.36/1.54  --splitting_mode                        input
% 7.36/1.54  --splitting_grd                         true
% 7.36/1.54  --splitting_cvd                         false
% 7.36/1.54  --splitting_cvd_svl                     false
% 7.36/1.54  --splitting_nvd                         32
% 7.36/1.54  --sub_typing                            true
% 7.36/1.54  --prep_gs_sim                           true
% 7.36/1.54  --prep_unflatten                        true
% 7.36/1.54  --prep_res_sim                          true
% 7.36/1.54  --prep_upred                            true
% 7.36/1.54  --prep_sem_filter                       exhaustive
% 7.36/1.54  --prep_sem_filter_out                   false
% 7.36/1.54  --pred_elim                             true
% 7.36/1.54  --res_sim_input                         true
% 7.36/1.54  --eq_ax_congr_red                       true
% 7.36/1.54  --pure_diseq_elim                       true
% 7.36/1.54  --brand_transform                       false
% 7.36/1.54  --non_eq_to_eq                          false
% 7.36/1.54  --prep_def_merge                        true
% 7.36/1.54  --prep_def_merge_prop_impl              false
% 7.36/1.54  --prep_def_merge_mbd                    true
% 7.36/1.54  --prep_def_merge_tr_red                 false
% 7.36/1.54  --prep_def_merge_tr_cl                  false
% 7.36/1.54  --smt_preprocessing                     true
% 7.36/1.54  --smt_ac_axioms                         fast
% 7.36/1.54  --preprocessed_out                      false
% 7.36/1.54  --preprocessed_stats                    false
% 7.36/1.54  
% 7.36/1.54  ------ Abstraction refinement Options
% 7.36/1.54  
% 7.36/1.54  --abstr_ref                             []
% 7.36/1.54  --abstr_ref_prep                        false
% 7.36/1.54  --abstr_ref_until_sat                   false
% 7.36/1.54  --abstr_ref_sig_restrict                funpre
% 7.36/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.54  --abstr_ref_under                       []
% 7.36/1.54  
% 7.36/1.54  ------ SAT Options
% 7.36/1.54  
% 7.36/1.54  --sat_mode                              false
% 7.36/1.54  --sat_fm_restart_options                ""
% 7.36/1.54  --sat_gr_def                            false
% 7.36/1.54  --sat_epr_types                         true
% 7.36/1.54  --sat_non_cyclic_types                  false
% 7.36/1.54  --sat_finite_models                     false
% 7.36/1.54  --sat_fm_lemmas                         false
% 7.36/1.54  --sat_fm_prep                           false
% 7.36/1.54  --sat_fm_uc_incr                        true
% 7.36/1.54  --sat_out_model                         small
% 7.36/1.54  --sat_out_clauses                       false
% 7.36/1.54  
% 7.36/1.54  ------ QBF Options
% 7.36/1.54  
% 7.36/1.54  --qbf_mode                              false
% 7.36/1.54  --qbf_elim_univ                         false
% 7.36/1.54  --qbf_dom_inst                          none
% 7.36/1.54  --qbf_dom_pre_inst                      false
% 7.36/1.54  --qbf_sk_in                             false
% 7.36/1.54  --qbf_pred_elim                         true
% 7.36/1.54  --qbf_split                             512
% 7.36/1.54  
% 7.36/1.54  ------ BMC1 Options
% 7.36/1.54  
% 7.36/1.54  --bmc1_incremental                      false
% 7.36/1.54  --bmc1_axioms                           reachable_all
% 7.36/1.54  --bmc1_min_bound                        0
% 7.36/1.54  --bmc1_max_bound                        -1
% 7.36/1.54  --bmc1_max_bound_default                -1
% 7.36/1.54  --bmc1_symbol_reachability              true
% 7.36/1.54  --bmc1_property_lemmas                  false
% 7.36/1.54  --bmc1_k_induction                      false
% 7.36/1.54  --bmc1_non_equiv_states                 false
% 7.36/1.54  --bmc1_deadlock                         false
% 7.36/1.54  --bmc1_ucm                              false
% 7.36/1.54  --bmc1_add_unsat_core                   none
% 7.36/1.54  --bmc1_unsat_core_children              false
% 7.36/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.54  --bmc1_out_stat                         full
% 7.36/1.54  --bmc1_ground_init                      false
% 7.36/1.54  --bmc1_pre_inst_next_state              false
% 7.36/1.54  --bmc1_pre_inst_state                   false
% 7.36/1.54  --bmc1_pre_inst_reach_state             false
% 7.36/1.54  --bmc1_out_unsat_core                   false
% 7.36/1.54  --bmc1_aig_witness_out                  false
% 7.36/1.54  --bmc1_verbose                          false
% 7.36/1.54  --bmc1_dump_clauses_tptp                false
% 7.36/1.54  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.54  --bmc1_dump_file                        -
% 7.36/1.54  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.54  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.54  --bmc1_ucm_extend_mode                  1
% 7.36/1.54  --bmc1_ucm_init_mode                    2
% 7.36/1.54  --bmc1_ucm_cone_mode                    none
% 7.36/1.54  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.54  --bmc1_ucm_relax_model                  4
% 7.36/1.54  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.54  --bmc1_ucm_layered_model                none
% 7.36/1.54  --bmc1_ucm_max_lemma_size               10
% 7.36/1.54  
% 7.36/1.54  ------ AIG Options
% 7.36/1.54  
% 7.36/1.54  --aig_mode                              false
% 7.36/1.54  
% 7.36/1.54  ------ Instantiation Options
% 7.36/1.54  
% 7.36/1.54  --instantiation_flag                    true
% 7.36/1.54  --inst_sos_flag                         false
% 7.36/1.54  --inst_sos_phase                        true
% 7.36/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.54  --inst_lit_sel_side                     num_symb
% 7.36/1.54  --inst_solver_per_active                1400
% 7.36/1.54  --inst_solver_calls_frac                1.
% 7.36/1.54  --inst_passive_queue_type               priority_queues
% 7.36/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.54  --inst_passive_queues_freq              [25;2]
% 7.36/1.54  --inst_dismatching                      true
% 7.36/1.54  --inst_eager_unprocessed_to_passive     true
% 7.36/1.54  --inst_prop_sim_given                   true
% 7.36/1.54  --inst_prop_sim_new                     false
% 7.36/1.54  --inst_subs_new                         false
% 7.36/1.54  --inst_eq_res_simp                      false
% 7.36/1.54  --inst_subs_given                       false
% 7.36/1.54  --inst_orphan_elimination               true
% 7.36/1.54  --inst_learning_loop_flag               true
% 7.36/1.54  --inst_learning_start                   3000
% 7.36/1.54  --inst_learning_factor                  2
% 7.36/1.54  --inst_start_prop_sim_after_learn       3
% 7.36/1.54  --inst_sel_renew                        solver
% 7.36/1.54  --inst_lit_activity_flag                true
% 7.36/1.54  --inst_restr_to_given                   false
% 7.36/1.54  --inst_activity_threshold               500
% 7.36/1.54  --inst_out_proof                        true
% 7.36/1.54  
% 7.36/1.54  ------ Resolution Options
% 7.36/1.54  
% 7.36/1.54  --resolution_flag                       true
% 7.36/1.54  --res_lit_sel                           adaptive
% 7.36/1.54  --res_lit_sel_side                      none
% 7.36/1.54  --res_ordering                          kbo
% 7.36/1.54  --res_to_prop_solver                    active
% 7.36/1.54  --res_prop_simpl_new                    false
% 7.36/1.54  --res_prop_simpl_given                  true
% 7.36/1.54  --res_passive_queue_type                priority_queues
% 7.36/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.54  --res_passive_queues_freq               [15;5]
% 7.36/1.54  --res_forward_subs                      full
% 7.36/1.54  --res_backward_subs                     full
% 7.36/1.54  --res_forward_subs_resolution           true
% 7.36/1.54  --res_backward_subs_resolution          true
% 7.36/1.54  --res_orphan_elimination                true
% 7.36/1.54  --res_time_limit                        2.
% 7.36/1.54  --res_out_proof                         true
% 7.36/1.54  
% 7.36/1.54  ------ Superposition Options
% 7.36/1.54  
% 7.36/1.54  --superposition_flag                    true
% 7.36/1.54  --sup_passive_queue_type                priority_queues
% 7.36/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.54  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.54  --demod_completeness_check              fast
% 7.36/1.54  --demod_use_ground                      true
% 7.36/1.54  --sup_to_prop_solver                    passive
% 7.36/1.54  --sup_prop_simpl_new                    true
% 7.36/1.54  --sup_prop_simpl_given                  true
% 7.36/1.54  --sup_fun_splitting                     false
% 7.36/1.54  --sup_smt_interval                      50000
% 7.36/1.54  
% 7.36/1.54  ------ Superposition Simplification Setup
% 7.36/1.54  
% 7.36/1.54  --sup_indices_passive                   []
% 7.36/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.54  --sup_full_bw                           [BwDemod]
% 7.36/1.54  --sup_immed_triv                        [TrivRules]
% 7.36/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.54  --sup_immed_bw_main                     []
% 7.36/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.36/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.36/1.54  
% 7.36/1.54  ------ Combination Options
% 7.36/1.54  
% 7.36/1.54  --comb_res_mult                         3
% 7.36/1.54  --comb_sup_mult                         2
% 7.36/1.54  --comb_inst_mult                        10
% 7.36/1.54  
% 7.36/1.54  ------ Debug Options
% 7.36/1.54  
% 7.36/1.54  --dbg_backtrace                         false
% 7.36/1.54  --dbg_dump_prop_clauses                 false
% 7.36/1.54  --dbg_dump_prop_clauses_file            -
% 7.36/1.54  --dbg_out_stat                          false
% 7.36/1.54  ------ Parsing...
% 7.36/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.36/1.54  
% 7.36/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.36/1.54  
% 7.36/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.36/1.54  
% 7.36/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.36/1.54  ------ Proving...
% 7.36/1.54  ------ Problem Properties 
% 7.36/1.54  
% 7.36/1.54  
% 7.36/1.54  clauses                                 31
% 7.36/1.54  conjectures                             2
% 7.36/1.54  EPR                                     6
% 7.36/1.54  Horn                                    31
% 7.36/1.54  unary                                   19
% 7.36/1.54  binary                                  10
% 7.36/1.54  lits                                    45
% 7.36/1.54  lits eq                                 21
% 7.36/1.54  fd_pure                                 0
% 7.36/1.54  fd_pseudo                               0
% 7.36/1.54  fd_cond                                 1
% 7.36/1.54  fd_pseudo_cond                          1
% 7.36/1.54  AC symbols                              2
% 7.36/1.54  
% 7.36/1.54  ------ Schedule dynamic 5 is on 
% 7.36/1.54  
% 7.36/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.36/1.54  
% 7.36/1.54  
% 7.36/1.54  ------ 
% 7.36/1.54  Current options:
% 7.36/1.54  ------ 
% 7.36/1.54  
% 7.36/1.54  ------ Input Options
% 7.36/1.54  
% 7.36/1.54  --out_options                           all
% 7.36/1.54  --tptp_safe_out                         true
% 7.36/1.54  --problem_path                          ""
% 7.36/1.54  --include_path                          ""
% 7.36/1.54  --clausifier                            res/vclausify_rel
% 7.36/1.54  --clausifier_options                    --mode clausify
% 7.36/1.54  --stdin                                 false
% 7.36/1.54  --stats_out                             all
% 7.36/1.54  
% 7.36/1.54  ------ General Options
% 7.36/1.54  
% 7.36/1.54  --fof                                   false
% 7.36/1.54  --time_out_real                         305.
% 7.36/1.54  --time_out_virtual                      -1.
% 7.36/1.54  --symbol_type_check                     false
% 7.36/1.54  --clausify_out                          false
% 7.36/1.54  --sig_cnt_out                           false
% 7.36/1.54  --trig_cnt_out                          false
% 7.36/1.54  --trig_cnt_out_tolerance                1.
% 7.36/1.54  --trig_cnt_out_sk_spl                   false
% 7.36/1.54  --abstr_cl_out                          false
% 7.36/1.54  
% 7.36/1.54  ------ Global Options
% 7.36/1.54  
% 7.36/1.54  --schedule                              default
% 7.36/1.54  --add_important_lit                     false
% 7.36/1.54  --prop_solver_per_cl                    1000
% 7.36/1.54  --min_unsat_core                        false
% 7.36/1.54  --soft_assumptions                      false
% 7.36/1.54  --soft_lemma_size                       3
% 7.36/1.54  --prop_impl_unit_size                   0
% 7.36/1.54  --prop_impl_unit                        []
% 7.36/1.54  --share_sel_clauses                     true
% 7.36/1.54  --reset_solvers                         false
% 7.36/1.54  --bc_imp_inh                            [conj_cone]
% 7.36/1.54  --conj_cone_tolerance                   3.
% 7.36/1.54  --extra_neg_conj                        none
% 7.36/1.54  --large_theory_mode                     true
% 7.36/1.54  --prolific_symb_bound                   200
% 7.36/1.54  --lt_threshold                          2000
% 7.36/1.54  --clause_weak_htbl                      true
% 7.36/1.54  --gc_record_bc_elim                     false
% 7.36/1.54  
% 7.36/1.54  ------ Preprocessing Options
% 7.36/1.54  
% 7.36/1.54  --preprocessing_flag                    true
% 7.36/1.54  --time_out_prep_mult                    0.1
% 7.36/1.54  --splitting_mode                        input
% 7.36/1.54  --splitting_grd                         true
% 7.36/1.54  --splitting_cvd                         false
% 7.36/1.54  --splitting_cvd_svl                     false
% 7.36/1.54  --splitting_nvd                         32
% 7.36/1.54  --sub_typing                            true
% 7.36/1.54  --prep_gs_sim                           true
% 7.36/1.54  --prep_unflatten                        true
% 7.36/1.54  --prep_res_sim                          true
% 7.36/1.54  --prep_upred                            true
% 7.36/1.54  --prep_sem_filter                       exhaustive
% 7.36/1.54  --prep_sem_filter_out                   false
% 7.36/1.54  --pred_elim                             true
% 7.36/1.54  --res_sim_input                         true
% 7.36/1.54  --eq_ax_congr_red                       true
% 7.36/1.54  --pure_diseq_elim                       true
% 7.36/1.54  --brand_transform                       false
% 7.36/1.54  --non_eq_to_eq                          false
% 7.36/1.54  --prep_def_merge                        true
% 7.36/1.54  --prep_def_merge_prop_impl              false
% 7.36/1.54  --prep_def_merge_mbd                    true
% 7.36/1.54  --prep_def_merge_tr_red                 false
% 7.36/1.54  --prep_def_merge_tr_cl                  false
% 7.36/1.54  --smt_preprocessing                     true
% 7.36/1.54  --smt_ac_axioms                         fast
% 7.36/1.54  --preprocessed_out                      false
% 7.36/1.54  --preprocessed_stats                    false
% 7.36/1.54  
% 7.36/1.54  ------ Abstraction refinement Options
% 7.36/1.54  
% 7.36/1.54  --abstr_ref                             []
% 7.36/1.54  --abstr_ref_prep                        false
% 7.36/1.54  --abstr_ref_until_sat                   false
% 7.36/1.54  --abstr_ref_sig_restrict                funpre
% 7.36/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.54  --abstr_ref_under                       []
% 7.36/1.54  
% 7.36/1.54  ------ SAT Options
% 7.36/1.54  
% 7.36/1.54  --sat_mode                              false
% 7.36/1.54  --sat_fm_restart_options                ""
% 7.36/1.54  --sat_gr_def                            false
% 7.36/1.54  --sat_epr_types                         true
% 7.36/1.54  --sat_non_cyclic_types                  false
% 7.36/1.54  --sat_finite_models                     false
% 7.36/1.54  --sat_fm_lemmas                         false
% 7.36/1.54  --sat_fm_prep                           false
% 7.36/1.54  --sat_fm_uc_incr                        true
% 7.36/1.54  --sat_out_model                         small
% 7.36/1.54  --sat_out_clauses                       false
% 7.36/1.54  
% 7.36/1.54  ------ QBF Options
% 7.36/1.54  
% 7.36/1.54  --qbf_mode                              false
% 7.36/1.54  --qbf_elim_univ                         false
% 7.36/1.54  --qbf_dom_inst                          none
% 7.36/1.54  --qbf_dom_pre_inst                      false
% 7.36/1.54  --qbf_sk_in                             false
% 7.36/1.54  --qbf_pred_elim                         true
% 7.36/1.54  --qbf_split                             512
% 7.36/1.54  
% 7.36/1.54  ------ BMC1 Options
% 7.36/1.54  
% 7.36/1.54  --bmc1_incremental                      false
% 7.36/1.54  --bmc1_axioms                           reachable_all
% 7.36/1.54  --bmc1_min_bound                        0
% 7.36/1.54  --bmc1_max_bound                        -1
% 7.36/1.54  --bmc1_max_bound_default                -1
% 7.36/1.54  --bmc1_symbol_reachability              true
% 7.36/1.54  --bmc1_property_lemmas                  false
% 7.36/1.54  --bmc1_k_induction                      false
% 7.36/1.54  --bmc1_non_equiv_states                 false
% 7.36/1.54  --bmc1_deadlock                         false
% 7.36/1.54  --bmc1_ucm                              false
% 7.36/1.54  --bmc1_add_unsat_core                   none
% 7.36/1.54  --bmc1_unsat_core_children              false
% 7.36/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.54  --bmc1_out_stat                         full
% 7.36/1.54  --bmc1_ground_init                      false
% 7.36/1.54  --bmc1_pre_inst_next_state              false
% 7.36/1.54  --bmc1_pre_inst_state                   false
% 7.36/1.54  --bmc1_pre_inst_reach_state             false
% 7.36/1.54  --bmc1_out_unsat_core                   false
% 7.36/1.54  --bmc1_aig_witness_out                  false
% 7.36/1.54  --bmc1_verbose                          false
% 7.36/1.54  --bmc1_dump_clauses_tptp                false
% 7.36/1.54  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.54  --bmc1_dump_file                        -
% 7.36/1.54  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.54  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.54  --bmc1_ucm_extend_mode                  1
% 7.36/1.54  --bmc1_ucm_init_mode                    2
% 7.36/1.54  --bmc1_ucm_cone_mode                    none
% 7.36/1.54  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.54  --bmc1_ucm_relax_model                  4
% 7.36/1.54  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.54  --bmc1_ucm_layered_model                none
% 7.36/1.54  --bmc1_ucm_max_lemma_size               10
% 7.36/1.54  
% 7.36/1.54  ------ AIG Options
% 7.36/1.54  
% 7.36/1.54  --aig_mode                              false
% 7.36/1.54  
% 7.36/1.54  ------ Instantiation Options
% 7.36/1.54  
% 7.36/1.54  --instantiation_flag                    true
% 7.36/1.54  --inst_sos_flag                         false
% 7.36/1.54  --inst_sos_phase                        true
% 7.36/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.54  --inst_lit_sel_side                     none
% 7.36/1.54  --inst_solver_per_active                1400
% 7.36/1.54  --inst_solver_calls_frac                1.
% 7.36/1.54  --inst_passive_queue_type               priority_queues
% 7.36/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.54  --inst_passive_queues_freq              [25;2]
% 7.36/1.54  --inst_dismatching                      true
% 7.36/1.54  --inst_eager_unprocessed_to_passive     true
% 7.36/1.54  --inst_prop_sim_given                   true
% 7.36/1.54  --inst_prop_sim_new                     false
% 7.36/1.54  --inst_subs_new                         false
% 7.36/1.54  --inst_eq_res_simp                      false
% 7.36/1.54  --inst_subs_given                       false
% 7.36/1.54  --inst_orphan_elimination               true
% 7.36/1.54  --inst_learning_loop_flag               true
% 7.36/1.54  --inst_learning_start                   3000
% 7.36/1.54  --inst_learning_factor                  2
% 7.36/1.54  --inst_start_prop_sim_after_learn       3
% 7.36/1.54  --inst_sel_renew                        solver
% 7.36/1.54  --inst_lit_activity_flag                true
% 7.36/1.54  --inst_restr_to_given                   false
% 7.36/1.54  --inst_activity_threshold               500
% 7.36/1.54  --inst_out_proof                        true
% 7.36/1.54  
% 7.36/1.54  ------ Resolution Options
% 7.36/1.54  
% 7.36/1.54  --resolution_flag                       false
% 7.36/1.54  --res_lit_sel                           adaptive
% 7.36/1.54  --res_lit_sel_side                      none
% 7.36/1.54  --res_ordering                          kbo
% 7.36/1.54  --res_to_prop_solver                    active
% 7.36/1.54  --res_prop_simpl_new                    false
% 7.36/1.54  --res_prop_simpl_given                  true
% 7.36/1.54  --res_passive_queue_type                priority_queues
% 7.36/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.54  --res_passive_queues_freq               [15;5]
% 7.36/1.54  --res_forward_subs                      full
% 7.36/1.54  --res_backward_subs                     full
% 7.36/1.54  --res_forward_subs_resolution           true
% 7.36/1.54  --res_backward_subs_resolution          true
% 7.36/1.54  --res_orphan_elimination                true
% 7.36/1.54  --res_time_limit                        2.
% 7.36/1.54  --res_out_proof                         true
% 7.36/1.54  
% 7.36/1.54  ------ Superposition Options
% 7.36/1.54  
% 7.36/1.54  --superposition_flag                    true
% 7.36/1.54  --sup_passive_queue_type                priority_queues
% 7.36/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.54  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.54  --demod_completeness_check              fast
% 7.36/1.54  --demod_use_ground                      true
% 7.36/1.54  --sup_to_prop_solver                    passive
% 7.36/1.54  --sup_prop_simpl_new                    true
% 7.36/1.54  --sup_prop_simpl_given                  true
% 7.36/1.54  --sup_fun_splitting                     false
% 7.36/1.54  --sup_smt_interval                      50000
% 7.36/1.54  
% 7.36/1.54  ------ Superposition Simplification Setup
% 7.36/1.54  
% 7.36/1.54  --sup_indices_passive                   []
% 7.36/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.54  --sup_full_bw                           [BwDemod]
% 7.36/1.54  --sup_immed_triv                        [TrivRules]
% 7.36/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.54  --sup_immed_bw_main                     []
% 7.36/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.36/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.36/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.36/1.54  
% 7.36/1.54  ------ Combination Options
% 7.36/1.54  
% 7.36/1.54  --comb_res_mult                         3
% 7.36/1.54  --comb_sup_mult                         2
% 7.36/1.54  --comb_inst_mult                        10
% 7.36/1.54  
% 7.36/1.54  ------ Debug Options
% 7.36/1.54  
% 7.36/1.54  --dbg_backtrace                         false
% 7.36/1.54  --dbg_dump_prop_clauses                 false
% 7.36/1.54  --dbg_dump_prop_clauses_file            -
% 7.36/1.54  --dbg_out_stat                          false
% 7.36/1.54  
% 7.36/1.54  
% 7.36/1.54  
% 7.36/1.54  
% 7.36/1.54  ------ Proving...
% 7.36/1.54  
% 7.36/1.54  
% 7.36/1.54  % SZS status Theorem for theBenchmark.p
% 7.36/1.54  
% 7.36/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 7.36/1.54  
% 7.36/1.54  fof(f29,axiom,(
% 7.36/1.54    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f84,plain,(
% 7.36/1.54    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.36/1.54    inference(cnf_transformation,[],[f29])).
% 7.36/1.54  
% 7.36/1.54  fof(f3,axiom,(
% 7.36/1.54    k1_xboole_0 = o_0_0_xboole_0),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f55,plain,(
% 7.36/1.54    k1_xboole_0 = o_0_0_xboole_0),
% 7.36/1.54    inference(cnf_transformation,[],[f3])).
% 7.36/1.54  
% 7.36/1.54  fof(f106,plain,(
% 7.36/1.54    ( ! [X0] : (k5_xboole_0(X0,X0) = o_0_0_xboole_0) )),
% 7.36/1.54    inference(definition_unfolding,[],[f84,f55])).
% 7.36/1.54  
% 7.36/1.54  fof(f28,axiom,(
% 7.36/1.54    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f83,plain,(
% 7.36/1.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.36/1.54    inference(cnf_transformation,[],[f28])).
% 7.36/1.54  
% 7.36/1.54  fof(f22,axiom,(
% 7.36/1.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f76,plain,(
% 7.36/1.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.36/1.54    inference(cnf_transformation,[],[f22])).
% 7.36/1.54  
% 7.36/1.54  fof(f101,plain,(
% 7.36/1.54    ( ! [X0] : (k5_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 7.36/1.54    inference(definition_unfolding,[],[f76,f55])).
% 7.36/1.54  
% 7.36/1.54  fof(f2,axiom,(
% 7.36/1.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f54,plain,(
% 7.36/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.36/1.54    inference(cnf_transformation,[],[f2])).
% 7.36/1.54  
% 7.36/1.54  fof(f15,axiom,(
% 7.36/1.54    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f69,plain,(
% 7.36/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.36/1.54    inference(cnf_transformation,[],[f15])).
% 7.36/1.54  
% 7.36/1.54  fof(f31,axiom,(
% 7.36/1.54    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f86,plain,(
% 7.36/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.36/1.54    inference(cnf_transformation,[],[f31])).
% 7.36/1.54  
% 7.36/1.54  fof(f12,axiom,(
% 7.36/1.54    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f66,plain,(
% 7.36/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.36/1.54    inference(cnf_transformation,[],[f12])).
% 7.36/1.54  
% 7.36/1.54  fof(f89,plain,(
% 7.36/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.36/1.54    inference(definition_unfolding,[],[f86,f66])).
% 7.36/1.54  
% 7.36/1.54  fof(f95,plain,(
% 7.36/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 7.36/1.54    inference(definition_unfolding,[],[f69,f89])).
% 7.36/1.54  
% 7.36/1.54  fof(f13,axiom,(
% 7.36/1.54    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f67,plain,(
% 7.36/1.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.36/1.54    inference(cnf_transformation,[],[f13])).
% 7.36/1.54  
% 7.36/1.54  fof(f1,axiom,(
% 7.36/1.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f53,plain,(
% 7.36/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.36/1.54    inference(cnf_transformation,[],[f1])).
% 7.36/1.54  
% 7.36/1.54  fof(f32,conjecture,(
% 7.36/1.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f33,negated_conjecture,(
% 7.36/1.54    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.36/1.54    inference(negated_conjecture,[],[f32])).
% 7.36/1.54  
% 7.36/1.54  fof(f46,plain,(
% 7.36/1.54    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.36/1.54    inference(ennf_transformation,[],[f33])).
% 7.36/1.54  
% 7.36/1.54  fof(f51,plain,(
% 7.36/1.54    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)) & r1_tarski(sK1,k4_xboole_0(sK2,sK3)))),
% 7.36/1.54    introduced(choice_axiom,[])).
% 7.36/1.54  
% 7.36/1.54  fof(f52,plain,(
% 7.36/1.54    (~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)) & r1_tarski(sK1,k4_xboole_0(sK2,sK3))),
% 7.36/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f51])).
% 7.36/1.54  
% 7.36/1.54  fof(f87,plain,(
% 7.36/1.54    r1_tarski(sK1,k4_xboole_0(sK2,sK3))),
% 7.36/1.54    inference(cnf_transformation,[],[f52])).
% 7.36/1.54  
% 7.36/1.54  fof(f108,plain,(
% 7.36/1.54    r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))),
% 7.36/1.54    inference(definition_unfolding,[],[f87,f66])).
% 7.36/1.54  
% 7.36/1.54  fof(f18,axiom,(
% 7.36/1.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f40,plain,(
% 7.36/1.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.36/1.54    inference(ennf_transformation,[],[f18])).
% 7.36/1.54  
% 7.36/1.54  fof(f72,plain,(
% 7.36/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.36/1.54    inference(cnf_transformation,[],[f40])).
% 7.36/1.54  
% 7.36/1.54  fof(f6,axiom,(
% 7.36/1.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f34,plain,(
% 7.36/1.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.36/1.54    inference(rectify,[],[f6])).
% 7.36/1.54  
% 7.36/1.54  fof(f59,plain,(
% 7.36/1.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.36/1.54    inference(cnf_transformation,[],[f34])).
% 7.36/1.54  
% 7.36/1.54  fof(f20,axiom,(
% 7.36/1.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f74,plain,(
% 7.36/1.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.36/1.54    inference(cnf_transformation,[],[f20])).
% 7.36/1.54  
% 7.36/1.54  fof(f99,plain,(
% 7.36/1.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 7.36/1.54    inference(definition_unfolding,[],[f74,f66,f66])).
% 7.36/1.54  
% 7.36/1.54  fof(f19,axiom,(
% 7.36/1.54    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f73,plain,(
% 7.36/1.54    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.36/1.54    inference(cnf_transformation,[],[f19])).
% 7.36/1.54  
% 7.36/1.54  fof(f98,plain,(
% 7.36/1.54    ( ! [X0] : (k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0) )),
% 7.36/1.54    inference(definition_unfolding,[],[f73,f55,f55])).
% 7.36/1.54  
% 7.36/1.54  fof(f14,axiom,(
% 7.36/1.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f68,plain,(
% 7.36/1.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.36/1.54    inference(cnf_transformation,[],[f14])).
% 7.36/1.54  
% 7.36/1.54  fof(f11,axiom,(
% 7.36/1.54    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 7.36/1.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.54  
% 7.36/1.54  fof(f65,plain,(
% 7.36/1.54    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 7.36/1.54    inference(cnf_transformation,[],[f11])).
% 7.36/1.54  
% 7.36/1.54  fof(f88,plain,(
% 7.36/1.54    ~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)),
% 7.36/1.54    inference(cnf_transformation,[],[f52])).
% 7.36/1.54  
% 7.36/1.54  cnf(c_29,plain,
% 7.36/1.54      ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
% 7.36/1.54      inference(cnf_transformation,[],[f106]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_28,plain,
% 7.36/1.54      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.36/1.54      inference(cnf_transformation,[],[f83]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_1489,plain,
% 7.36/1.54      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_29,c_28]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_21,plain,
% 7.36/1.54      ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
% 7.36/1.54      inference(cnf_transformation,[],[f101]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_1,plain,
% 7.36/1.54      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.36/1.54      inference(cnf_transformation,[],[f54]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_1320,plain,
% 7.36/1.54      ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_21,c_1]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_2298,plain,
% 7.36/1.54      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.36/1.54      inference(demodulation,[status(thm)],[c_1489,c_1320]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_2303,plain,
% 7.36/1.54      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_1,c_2298]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_2400,plain,
% 7.36/1.54      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_2298,c_2303]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_2443,plain,
% 7.36/1.54      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_2400,c_28]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_14,plain,
% 7.36/1.54      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.36/1.54      inference(cnf_transformation,[],[f95]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_12,plain,
% 7.36/1.54      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.36/1.54      inference(cnf_transformation,[],[f67]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_0,plain,
% 7.36/1.54      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.36/1.54      inference(cnf_transformation,[],[f53]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_501,plain,
% 7.36/1.54      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 7.36/1.54      inference(theory_normalisation,
% 7.36/1.54                [status(thm)],
% 7.36/1.54                [c_14,c_28,c_1,c_12,c_0]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_32,negated_conjecture,
% 7.36/1.54      ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
% 7.36/1.54      inference(cnf_transformation,[],[f108]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_494,negated_conjecture,
% 7.36/1.54      ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) ),
% 7.36/1.54      inference(theory_normalisation,
% 7.36/1.54                [status(thm)],
% 7.36/1.54                [c_32,c_28,c_1,c_12,c_0]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_927,plain,
% 7.36/1.54      ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = iProver_top ),
% 7.36/1.54      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_17,plain,
% 7.36/1.54      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.36/1.54      inference(cnf_transformation,[],[f72]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_935,plain,
% 7.36/1.54      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.36/1.54      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_27020,plain,
% 7.36/1.54      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = sK1 ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_927,c_935]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_29446,plain,
% 7.36/1.54      ( k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)) = k3_xboole_0(sK1,X0) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_27020,c_12]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_33554,plain,
% 7.36/1.54      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_501,c_29446]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_33913,plain,
% 7.36/1.54      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))) = sK1 ),
% 7.36/1.54      inference(light_normalisation,[status(thm)],[c_33554,c_27020]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_41112,plain,
% 7.36/1.54      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(sK3,sK2)))) = sK1 ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_2443,c_33913]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_5,plain,
% 7.36/1.54      ( k3_xboole_0(X0,X0) = X0 ),
% 7.36/1.54      inference(cnf_transformation,[],[f59]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_1471,plain,
% 7.36/1.54      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_5,c_12]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_2266,plain,
% 7.36/1.54      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_0,c_1471]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_19,plain,
% 7.36/1.54      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.36/1.54      inference(cnf_transformation,[],[f99]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_498,plain,
% 7.36/1.54      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.36/1.54      inference(theory_normalisation,
% 7.36/1.54                [status(thm)],
% 7.36/1.54                [c_19,c_28,c_1,c_12,c_0]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_3224,plain,
% 7.36/1.54      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_2266,c_498]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_3277,plain,
% 7.36/1.54      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
% 7.36/1.54      inference(demodulation,[status(thm)],[c_3224,c_29]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_3837,plain,
% 7.36/1.54      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = o_0_0_xboole_0 ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_0,c_3277]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_4546,plain,
% 7.36/1.54      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),o_0_0_xboole_0) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_3837,c_2266]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_18,plain,
% 7.36/1.54      ( k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 7.36/1.54      inference(cnf_transformation,[],[f98]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_4562,plain,
% 7.36/1.54      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = o_0_0_xboole_0 ),
% 7.36/1.54      inference(demodulation,[status(thm)],[c_4546,c_18]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_4922,plain,
% 7.36/1.54      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X1,X2)) = k3_xboole_0(o_0_0_xboole_0,X2) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_4562,c_12]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_1315,plain,
% 7.36/1.54      ( k3_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_18,c_0]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_4946,plain,
% 7.36/1.54      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(X1,X2)) = o_0_0_xboole_0 ),
% 7.36/1.54      inference(demodulation,[status(thm)],[c_4922,c_1315]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_41465,plain,
% 7.36/1.54      ( k3_xboole_0(sK1,sK2) = sK1 ),
% 7.36/1.54      inference(demodulation,[status(thm)],[c_41112,c_21,c_4946]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_13,plain,
% 7.36/1.54      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.36/1.54      inference(cnf_transformation,[],[f68]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_936,plain,
% 7.36/1.54      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 7.36/1.54      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_1589,plain,
% 7.36/1.54      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_0,c_936]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_42587,plain,
% 7.36/1.54      ( r1_tarski(sK1,sK2) = iProver_top ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_41465,c_1589]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_1050,plain,
% 7.36/1.54      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_5745,plain,
% 7.36/1.54      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,X2)))) = k3_xboole_0(X1,o_0_0_xboole_0) ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_3837,c_1050]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_5886,plain,
% 7.36/1.54      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,X2)))) = o_0_0_xboole_0 ),
% 7.36/1.54      inference(demodulation,[status(thm)],[c_5745,c_18]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_29494,plain,
% 7.36/1.54      ( k3_xboole_0(sK3,sK1) = o_0_0_xboole_0 ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_27020,c_5886]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_11,plain,
% 7.36/1.54      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 7.36/1.54      inference(cnf_transformation,[],[f65]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_937,plain,
% 7.36/1.54      ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 7.36/1.54      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_2309,plain,
% 7.36/1.54      ( r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_2298,c_937]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_5390,plain,
% 7.36/1.54      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_501,c_2309]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_6198,plain,
% 7.36/1.54      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k5_xboole_0(X1,o_0_0_xboole_0)) = iProver_top ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_4562,c_5390]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_6200,plain,
% 7.36/1.54      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 7.36/1.54      inference(demodulation,[status(thm)],[c_6198,c_21]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_29866,plain,
% 7.36/1.54      ( r1_xboole_0(k5_xboole_0(sK1,o_0_0_xboole_0),sK3) = iProver_top ),
% 7.36/1.54      inference(superposition,[status(thm)],[c_29494,c_6200]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_29980,plain,
% 7.36/1.54      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 7.36/1.54      inference(demodulation,[status(thm)],[c_29866,c_21]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_31,negated_conjecture,
% 7.36/1.54      ( ~ r1_tarski(sK1,sK2) | ~ r1_xboole_0(sK1,sK3) ),
% 7.36/1.54      inference(cnf_transformation,[],[f88]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(c_34,plain,
% 7.36/1.54      ( r1_tarski(sK1,sK2) != iProver_top
% 7.36/1.54      | r1_xboole_0(sK1,sK3) != iProver_top ),
% 7.36/1.54      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.36/1.54  
% 7.36/1.54  cnf(contradiction,plain,
% 7.36/1.54      ( $false ),
% 7.36/1.54      inference(minisat,[status(thm)],[c_42587,c_29980,c_34]) ).
% 7.36/1.54  
% 7.36/1.54  
% 7.36/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 7.36/1.54  
% 7.36/1.54  ------                               Statistics
% 7.36/1.54  
% 7.36/1.54  ------ General
% 7.36/1.54  
% 7.36/1.54  abstr_ref_over_cycles:                  0
% 7.36/1.54  abstr_ref_under_cycles:                 0
% 7.36/1.54  gc_basic_clause_elim:                   0
% 7.36/1.54  forced_gc_time:                         0
% 7.36/1.54  parsing_time:                           0.012
% 7.36/1.54  unif_index_cands_time:                  0.
% 7.36/1.54  unif_index_add_time:                    0.
% 7.36/1.54  orderings_time:                         0.
% 7.36/1.54  out_proof_time:                         0.01
% 7.36/1.54  total_time:                             1.051
% 7.36/1.54  num_of_symbols:                         42
% 7.36/1.54  num_of_terms:                           49298
% 7.36/1.54  
% 7.36/1.54  ------ Preprocessing
% 7.36/1.54  
% 7.36/1.54  num_of_splits:                          0
% 7.36/1.54  num_of_split_atoms:                     0
% 7.36/1.54  num_of_reused_defs:                     0
% 7.36/1.54  num_eq_ax_congr_red:                    2
% 7.36/1.54  num_of_sem_filtered_clauses:            1
% 7.36/1.54  num_of_subtypes:                        0
% 7.36/1.54  monotx_restored_types:                  0
% 7.36/1.54  sat_num_of_epr_types:                   0
% 7.36/1.54  sat_num_of_non_cyclic_types:            0
% 7.36/1.54  sat_guarded_non_collapsed_types:        0
% 7.36/1.54  num_pure_diseq_elim:                    0
% 7.36/1.54  simp_replaced_by:                       0
% 7.36/1.54  res_preprocessed:                       139
% 7.36/1.54  prep_upred:                             0
% 7.36/1.54  prep_unflattend:                        3
% 7.36/1.54  smt_new_axioms:                         0
% 7.36/1.54  pred_elim_cands:                        2
% 7.36/1.54  pred_elim:                              2
% 7.36/1.54  pred_elim_cl:                           2
% 7.36/1.54  pred_elim_cycles:                       4
% 7.36/1.54  merged_defs:                            16
% 7.36/1.54  merged_defs_ncl:                        0
% 7.36/1.54  bin_hyper_res:                          16
% 7.36/1.54  prep_cycles:                            4
% 7.36/1.54  pred_elim_time:                         0.001
% 7.36/1.54  splitting_time:                         0.
% 7.36/1.54  sem_filter_time:                        0.
% 7.36/1.54  monotx_time:                            0.001
% 7.36/1.54  subtype_inf_time:                       0.
% 7.36/1.54  
% 7.36/1.54  ------ Problem properties
% 7.36/1.54  
% 7.36/1.54  clauses:                                31
% 7.36/1.54  conjectures:                            2
% 7.36/1.54  epr:                                    6
% 7.36/1.54  horn:                                   31
% 7.36/1.54  ground:                                 4
% 7.36/1.54  unary:                                  19
% 7.36/1.54  binary:                                 10
% 7.36/1.54  lits:                                   45
% 7.36/1.54  lits_eq:                                21
% 7.36/1.54  fd_pure:                                0
% 7.36/1.54  fd_pseudo:                              0
% 7.36/1.54  fd_cond:                                1
% 7.36/1.54  fd_pseudo_cond:                         1
% 7.36/1.54  ac_symbols:                             2
% 7.36/1.54  
% 7.36/1.54  ------ Propositional Solver
% 7.36/1.54  
% 7.36/1.54  prop_solver_calls:                      29
% 7.36/1.54  prop_fast_solver_calls:                 629
% 7.36/1.54  smt_solver_calls:                       0
% 7.36/1.54  smt_fast_solver_calls:                  0
% 7.36/1.54  prop_num_of_clauses:                    11962
% 7.36/1.54  prop_preprocess_simplified:             15627
% 7.36/1.54  prop_fo_subsumed:                       0
% 7.36/1.54  prop_solver_time:                       0.
% 7.36/1.54  smt_solver_time:                        0.
% 7.36/1.54  smt_fast_solver_time:                   0.
% 7.36/1.54  prop_fast_solver_time:                  0.
% 7.36/1.54  prop_unsat_core_time:                   0.001
% 7.36/1.54  
% 7.36/1.54  ------ QBF
% 7.36/1.54  
% 7.36/1.54  qbf_q_res:                              0
% 7.36/1.54  qbf_num_tautologies:                    0
% 7.36/1.54  qbf_prep_cycles:                        0
% 7.36/1.54  
% 7.36/1.54  ------ BMC1
% 7.36/1.54  
% 7.36/1.54  bmc1_current_bound:                     -1
% 7.36/1.54  bmc1_last_solved_bound:                 -1
% 7.36/1.54  bmc1_unsat_core_size:                   -1
% 7.36/1.54  bmc1_unsat_core_parents_size:           -1
% 7.36/1.54  bmc1_merge_next_fun:                    0
% 7.36/1.54  bmc1_unsat_core_clauses_time:           0.
% 7.36/1.54  
% 7.36/1.54  ------ Instantiation
% 7.36/1.54  
% 7.36/1.54  inst_num_of_clauses:                    2028
% 7.36/1.54  inst_num_in_passive:                    742
% 7.36/1.54  inst_num_in_active:                     744
% 7.36/1.54  inst_num_in_unprocessed:                542
% 7.36/1.54  inst_num_of_loops:                      790
% 7.36/1.54  inst_num_of_learning_restarts:          0
% 7.36/1.54  inst_num_moves_active_passive:          44
% 7.36/1.54  inst_lit_activity:                      0
% 7.36/1.54  inst_lit_activity_moves:                0
% 7.36/1.54  inst_num_tautologies:                   0
% 7.36/1.54  inst_num_prop_implied:                  0
% 7.36/1.54  inst_num_existing_simplified:           0
% 7.36/1.54  inst_num_eq_res_simplified:             0
% 7.36/1.54  inst_num_child_elim:                    0
% 7.36/1.54  inst_num_of_dismatching_blockings:      1643
% 7.36/1.54  inst_num_of_non_proper_insts:           2597
% 7.36/1.54  inst_num_of_duplicates:                 0
% 7.36/1.54  inst_inst_num_from_inst_to_res:         0
% 7.36/1.54  inst_dismatching_checking_time:         0.
% 7.36/1.54  
% 7.36/1.54  ------ Resolution
% 7.36/1.54  
% 7.36/1.54  res_num_of_clauses:                     0
% 7.36/1.54  res_num_in_passive:                     0
% 7.36/1.54  res_num_in_active:                      0
% 7.36/1.54  res_num_of_loops:                       143
% 7.36/1.54  res_forward_subset_subsumed:            225
% 7.36/1.54  res_backward_subset_subsumed:           0
% 7.36/1.54  res_forward_subsumed:                   0
% 7.36/1.54  res_backward_subsumed:                  0
% 7.36/1.54  res_forward_subsumption_resolution:     0
% 7.36/1.54  res_backward_subsumption_resolution:    0
% 7.36/1.54  res_clause_to_clause_subsumption:       38943
% 7.36/1.54  res_orphan_elimination:                 0
% 7.36/1.54  res_tautology_del:                      167
% 7.36/1.54  res_num_eq_res_simplified:              0
% 7.36/1.54  res_num_sel_changes:                    0
% 7.36/1.54  res_moves_from_active_to_pass:          0
% 7.36/1.54  
% 7.36/1.54  ------ Superposition
% 7.36/1.54  
% 7.36/1.54  sup_time_total:                         0.
% 7.36/1.54  sup_time_generating:                    0.
% 7.36/1.54  sup_time_sim_full:                      0.
% 7.36/1.54  sup_time_sim_immed:                     0.
% 7.36/1.54  
% 7.36/1.54  sup_num_of_clauses:                     2922
% 7.36/1.54  sup_num_in_active:                      156
% 7.36/1.54  sup_num_in_passive:                     2766
% 7.36/1.54  sup_num_of_loops:                       156
% 7.36/1.54  sup_fw_superposition:                   5185
% 7.36/1.54  sup_bw_superposition:                   5576
% 7.36/1.54  sup_immediate_simplified:               4605
% 7.36/1.54  sup_given_eliminated:                   0
% 7.36/1.54  comparisons_done:                       0
% 7.36/1.54  comparisons_avoided:                    0
% 7.36/1.54  
% 7.36/1.54  ------ Simplifications
% 7.36/1.54  
% 7.36/1.54  
% 7.36/1.54  sim_fw_subset_subsumed:                 32
% 7.36/1.54  sim_bw_subset_subsumed:                 4
% 7.36/1.54  sim_fw_subsumed:                        873
% 7.36/1.54  sim_bw_subsumed:                        29
% 7.36/1.54  sim_fw_subsumption_res:                 0
% 7.36/1.54  sim_bw_subsumption_res:                 0
% 7.36/1.54  sim_tautology_del:                      23
% 7.36/1.54  sim_eq_tautology_del:                   357
% 7.36/1.54  sim_eq_res_simp:                        0
% 7.36/1.54  sim_fw_demodulated:                     2260
% 7.36/1.54  sim_bw_demodulated:                     103
% 7.36/1.54  sim_light_normalised:                   1829
% 7.36/1.54  sim_joinable_taut:                      75
% 7.36/1.54  sim_joinable_simp:                      0
% 7.36/1.54  sim_ac_normalised:                      0
% 7.36/1.54  sim_smt_subsumption:                    0
% 7.36/1.54  
%------------------------------------------------------------------------------
