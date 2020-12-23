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
% DateTime   : Thu Dec  3 11:24:58 EST 2020

% Result     : Theorem 11.34s
% Output     : CNFRefutation 11.34s
% Verified   : 
% Statistics : Number of formulae       :  149 (9832 expanded)
%              Number of clauses        :  112 (4169 expanded)
%              Number of leaves         :   14 (2617 expanded)
%              Depth                    :   30
%              Number of atoms          :  156 (9863 expanded)
%              Number of equality atoms :  143 (9818 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f28,f28])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f23,f28])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f24,f28,f23])).

fof(f14,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f18,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f19,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f34,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f34,f23,f23,f28])).

cnf(c_8,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_135,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_134,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_383,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_135,c_134])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1774,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_383,c_5])).

cnf(c_1788,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1774,c_5])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_4,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_386,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1142,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_386,c_6])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1149,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_386,c_1])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_389,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_390,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_389,c_3])).

cnf(c_564,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_390])).

cnf(c_609,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_564,c_4])).

cnf(c_550,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_6])).

cnf(c_741,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_609,c_550])).

cnf(c_829,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_741,c_6])).

cnf(c_833,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_829,c_609])).

cnf(c_939,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_833,c_5])).

cnf(c_942,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_939,c_829])).

cnf(c_1152,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1149,c_3,c_942])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1147,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_386,c_10])).

cnf(c_1155,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1147,c_3,c_942])).

cnf(c_1156,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_1155,c_564])).

cnf(c_1158,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1142,c_1152,c_1156])).

cnf(c_41542,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_1788,c_1158])).

cnf(c_1353,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_942])).

cnf(c_1508,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_1353])).

cnf(c_1626,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_1508])).

cnf(c_7519,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1626,c_5])).

cnf(c_2058,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_1158])).

cnf(c_1635,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1508,c_10])).

cnf(c_1660,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_1635,c_5,c_564])).

cnf(c_1661,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1660,c_6,c_390])).

cnf(c_2085,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2058,c_1661])).

cnf(c_23164,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_7519,c_2085])).

cnf(c_1950,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1152,c_6])).

cnf(c_1966,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1950,c_386])).

cnf(c_4288,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1353,c_1966])).

cnf(c_1646,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1508,c_10])).

cnf(c_1648,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1508,c_1])).

cnf(c_1651,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1648,c_5,c_390])).

cnf(c_1654,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1646,c_1651])).

cnf(c_1655,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_1654,c_6,c_390])).

cnf(c_1944,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1152,c_1655])).

cnf(c_4175,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1944])).

cnf(c_4334,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_4288,c_4175])).

cnf(c_5405,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1158,c_4334])).

cnf(c_5457,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_5405,c_4334])).

cnf(c_466,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_478,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_466,c_5])).

cnf(c_15952,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
    inference(superposition,[status(thm)],[c_2085,c_478])).

cnf(c_16080,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_15952,c_2085])).

cnf(c_23225,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_23164,c_3,c_5457,c_16080])).

cnf(c_1144,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_386,c_5])).

cnf(c_1157,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_1144,c_5])).

cnf(c_36285,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1157,c_1158])).

cnf(c_467,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_477,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_467,c_5])).

cnf(c_13650,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_477,c_942])).

cnf(c_34895,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_13650,c_2085])).

cnf(c_2060,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_1158])).

cnf(c_2084,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2060,c_1158])).

cnf(c_1919,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_1152])).

cnf(c_4458,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2084,c_1919])).

cnf(c_4484,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_4458,c_1353])).

cnf(c_34976,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1)),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_34895,c_4484])).

cnf(c_554,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_7483,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1626,c_554])).

cnf(c_7561,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_7483,c_5,c_564])).

cnf(c_5413,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4334,c_4175])).

cnf(c_2,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_136,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1148,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_386,c_136])).

cnf(c_1153,plain,
    ( r1_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1148,c_3,c_942])).

cnf(c_1154,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1153,c_564])).

cnf(c_1394,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1154,c_134])).

cnf(c_1545,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_1394])).

cnf(c_1808,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_1661])).

cnf(c_3007,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1545,c_1808])).

cnf(c_4714,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2084,c_3007])).

cnf(c_4750,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4714,c_3007])).

cnf(c_5452,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5413,c_4750])).

cnf(c_7562,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_7561,c_477,c_5452])).

cnf(c_30348,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_7562,c_1966])).

cnf(c_34977,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_34976,c_1157,c_30348])).

cnf(c_36381,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_36285,c_34977])).

cnf(c_41647,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_41542,c_23225,c_36381])).

cnf(c_1942,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1152,c_1661])).

cnf(c_11,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_138,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11,c_5])).

cnf(c_223,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_0,c_138])).

cnf(c_3440,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1942,c_223])).

cnf(c_1105,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_10,c_4])).

cnf(c_3441,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3440,c_1105])).

cnf(c_1922,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_1152])).

cnf(c_974,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_136,c_134])).

cnf(c_1984,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1922,c_974])).

cnf(c_3442,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3441,c_1966,c_1984])).

cnf(c_58973,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_41647,c_3442])).

cnf(c_1558,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1394,c_5])).

cnf(c_7273,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,X0),X1)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_1558,c_5457])).

cnf(c_58977,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_58973,c_1661,c_7273])).

cnf(c_288,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58977,c_288])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:33:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.34/2.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.34/2.03  
% 11.34/2.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.34/2.03  
% 11.34/2.03  ------  iProver source info
% 11.34/2.03  
% 11.34/2.03  git: date: 2020-06-30 10:37:57 +0100
% 11.34/2.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.34/2.03  git: non_committed_changes: false
% 11.34/2.03  git: last_make_outside_of_git: false
% 11.34/2.03  
% 11.34/2.03  ------ 
% 11.34/2.03  
% 11.34/2.03  ------ Input Options
% 11.34/2.03  
% 11.34/2.03  --out_options                           all
% 11.34/2.03  --tptp_safe_out                         true
% 11.34/2.03  --problem_path                          ""
% 11.34/2.03  --include_path                          ""
% 11.34/2.03  --clausifier                            res/vclausify_rel
% 11.34/2.03  --clausifier_options                    ""
% 11.34/2.03  --stdin                                 false
% 11.34/2.03  --stats_out                             all
% 11.34/2.03  
% 11.34/2.03  ------ General Options
% 11.34/2.03  
% 11.34/2.03  --fof                                   false
% 11.34/2.03  --time_out_real                         305.
% 11.34/2.03  --time_out_virtual                      -1.
% 11.34/2.03  --symbol_type_check                     false
% 11.34/2.03  --clausify_out                          false
% 11.34/2.03  --sig_cnt_out                           false
% 11.34/2.03  --trig_cnt_out                          false
% 11.34/2.03  --trig_cnt_out_tolerance                1.
% 11.34/2.03  --trig_cnt_out_sk_spl                   false
% 11.34/2.03  --abstr_cl_out                          false
% 11.34/2.03  
% 11.34/2.03  ------ Global Options
% 11.34/2.03  
% 11.34/2.03  --schedule                              default
% 11.34/2.03  --add_important_lit                     false
% 11.34/2.03  --prop_solver_per_cl                    1000
% 11.34/2.03  --min_unsat_core                        false
% 11.34/2.03  --soft_assumptions                      false
% 11.34/2.03  --soft_lemma_size                       3
% 11.34/2.03  --prop_impl_unit_size                   0
% 11.34/2.03  --prop_impl_unit                        []
% 11.34/2.03  --share_sel_clauses                     true
% 11.34/2.03  --reset_solvers                         false
% 11.34/2.03  --bc_imp_inh                            [conj_cone]
% 11.34/2.03  --conj_cone_tolerance                   3.
% 11.34/2.03  --extra_neg_conj                        none
% 11.34/2.03  --large_theory_mode                     true
% 11.34/2.03  --prolific_symb_bound                   200
% 11.34/2.03  --lt_threshold                          2000
% 11.34/2.03  --clause_weak_htbl                      true
% 11.34/2.03  --gc_record_bc_elim                     false
% 11.34/2.03  
% 11.34/2.03  ------ Preprocessing Options
% 11.34/2.03  
% 11.34/2.03  --preprocessing_flag                    true
% 11.34/2.03  --time_out_prep_mult                    0.1
% 11.34/2.03  --splitting_mode                        input
% 11.34/2.03  --splitting_grd                         true
% 11.34/2.03  --splitting_cvd                         false
% 11.34/2.03  --splitting_cvd_svl                     false
% 11.34/2.03  --splitting_nvd                         32
% 11.34/2.03  --sub_typing                            true
% 11.34/2.03  --prep_gs_sim                           true
% 11.34/2.03  --prep_unflatten                        true
% 11.34/2.03  --prep_res_sim                          true
% 11.34/2.03  --prep_upred                            true
% 11.34/2.03  --prep_sem_filter                       exhaustive
% 11.34/2.03  --prep_sem_filter_out                   false
% 11.34/2.03  --pred_elim                             true
% 11.34/2.03  --res_sim_input                         true
% 11.34/2.03  --eq_ax_congr_red                       true
% 11.34/2.03  --pure_diseq_elim                       true
% 11.34/2.03  --brand_transform                       false
% 11.34/2.03  --non_eq_to_eq                          false
% 11.34/2.03  --prep_def_merge                        true
% 11.34/2.03  --prep_def_merge_prop_impl              false
% 11.34/2.03  --prep_def_merge_mbd                    true
% 11.34/2.03  --prep_def_merge_tr_red                 false
% 11.34/2.03  --prep_def_merge_tr_cl                  false
% 11.34/2.03  --smt_preprocessing                     true
% 11.34/2.03  --smt_ac_axioms                         fast
% 11.34/2.03  --preprocessed_out                      false
% 11.34/2.03  --preprocessed_stats                    false
% 11.34/2.03  
% 11.34/2.03  ------ Abstraction refinement Options
% 11.34/2.03  
% 11.34/2.03  --abstr_ref                             []
% 11.34/2.03  --abstr_ref_prep                        false
% 11.34/2.03  --abstr_ref_until_sat                   false
% 11.34/2.03  --abstr_ref_sig_restrict                funpre
% 11.34/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.34/2.03  --abstr_ref_under                       []
% 11.34/2.03  
% 11.34/2.03  ------ SAT Options
% 11.34/2.03  
% 11.34/2.03  --sat_mode                              false
% 11.34/2.03  --sat_fm_restart_options                ""
% 11.34/2.03  --sat_gr_def                            false
% 11.34/2.03  --sat_epr_types                         true
% 11.34/2.03  --sat_non_cyclic_types                  false
% 11.34/2.03  --sat_finite_models                     false
% 11.34/2.03  --sat_fm_lemmas                         false
% 11.34/2.03  --sat_fm_prep                           false
% 11.34/2.03  --sat_fm_uc_incr                        true
% 11.34/2.03  --sat_out_model                         small
% 11.34/2.03  --sat_out_clauses                       false
% 11.34/2.03  
% 11.34/2.03  ------ QBF Options
% 11.34/2.03  
% 11.34/2.03  --qbf_mode                              false
% 11.34/2.03  --qbf_elim_univ                         false
% 11.34/2.03  --qbf_dom_inst                          none
% 11.34/2.03  --qbf_dom_pre_inst                      false
% 11.34/2.03  --qbf_sk_in                             false
% 11.34/2.03  --qbf_pred_elim                         true
% 11.34/2.03  --qbf_split                             512
% 11.34/2.03  
% 11.34/2.03  ------ BMC1 Options
% 11.34/2.03  
% 11.34/2.03  --bmc1_incremental                      false
% 11.34/2.03  --bmc1_axioms                           reachable_all
% 11.34/2.03  --bmc1_min_bound                        0
% 11.34/2.03  --bmc1_max_bound                        -1
% 11.34/2.03  --bmc1_max_bound_default                -1
% 11.34/2.03  --bmc1_symbol_reachability              true
% 11.34/2.03  --bmc1_property_lemmas                  false
% 11.34/2.03  --bmc1_k_induction                      false
% 11.34/2.03  --bmc1_non_equiv_states                 false
% 11.34/2.03  --bmc1_deadlock                         false
% 11.34/2.03  --bmc1_ucm                              false
% 11.34/2.03  --bmc1_add_unsat_core                   none
% 11.34/2.03  --bmc1_unsat_core_children              false
% 11.34/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.34/2.03  --bmc1_out_stat                         full
% 11.34/2.03  --bmc1_ground_init                      false
% 11.34/2.03  --bmc1_pre_inst_next_state              false
% 11.34/2.03  --bmc1_pre_inst_state                   false
% 11.34/2.03  --bmc1_pre_inst_reach_state             false
% 11.34/2.03  --bmc1_out_unsat_core                   false
% 11.34/2.03  --bmc1_aig_witness_out                  false
% 11.34/2.03  --bmc1_verbose                          false
% 11.34/2.03  --bmc1_dump_clauses_tptp                false
% 11.34/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.34/2.03  --bmc1_dump_file                        -
% 11.34/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.34/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.34/2.03  --bmc1_ucm_extend_mode                  1
% 11.34/2.03  --bmc1_ucm_init_mode                    2
% 11.34/2.03  --bmc1_ucm_cone_mode                    none
% 11.34/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.34/2.03  --bmc1_ucm_relax_model                  4
% 11.34/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.34/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.34/2.03  --bmc1_ucm_layered_model                none
% 11.34/2.03  --bmc1_ucm_max_lemma_size               10
% 11.34/2.03  
% 11.34/2.03  ------ AIG Options
% 11.34/2.03  
% 11.34/2.03  --aig_mode                              false
% 11.34/2.03  
% 11.34/2.03  ------ Instantiation Options
% 11.34/2.03  
% 11.34/2.03  --instantiation_flag                    true
% 11.34/2.03  --inst_sos_flag                         true
% 11.34/2.03  --inst_sos_phase                        true
% 11.34/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.34/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.34/2.03  --inst_lit_sel_side                     num_symb
% 11.34/2.03  --inst_solver_per_active                1400
% 11.34/2.03  --inst_solver_calls_frac                1.
% 11.34/2.03  --inst_passive_queue_type               priority_queues
% 11.34/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.34/2.03  --inst_passive_queues_freq              [25;2]
% 11.34/2.03  --inst_dismatching                      true
% 11.34/2.03  --inst_eager_unprocessed_to_passive     true
% 11.34/2.03  --inst_prop_sim_given                   true
% 11.34/2.03  --inst_prop_sim_new                     false
% 11.34/2.03  --inst_subs_new                         false
% 11.34/2.03  --inst_eq_res_simp                      false
% 11.34/2.03  --inst_subs_given                       false
% 11.34/2.03  --inst_orphan_elimination               true
% 11.34/2.03  --inst_learning_loop_flag               true
% 11.34/2.03  --inst_learning_start                   3000
% 11.34/2.03  --inst_learning_factor                  2
% 11.34/2.03  --inst_start_prop_sim_after_learn       3
% 11.34/2.03  --inst_sel_renew                        solver
% 11.34/2.03  --inst_lit_activity_flag                true
% 11.34/2.03  --inst_restr_to_given                   false
% 11.34/2.03  --inst_activity_threshold               500
% 11.34/2.03  --inst_out_proof                        true
% 11.34/2.03  
% 11.34/2.03  ------ Resolution Options
% 11.34/2.03  
% 11.34/2.03  --resolution_flag                       true
% 11.34/2.03  --res_lit_sel                           adaptive
% 11.34/2.03  --res_lit_sel_side                      none
% 11.34/2.03  --res_ordering                          kbo
% 11.34/2.03  --res_to_prop_solver                    active
% 11.34/2.03  --res_prop_simpl_new                    false
% 11.34/2.03  --res_prop_simpl_given                  true
% 11.34/2.03  --res_passive_queue_type                priority_queues
% 11.34/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.34/2.03  --res_passive_queues_freq               [15;5]
% 11.34/2.03  --res_forward_subs                      full
% 11.34/2.03  --res_backward_subs                     full
% 11.34/2.03  --res_forward_subs_resolution           true
% 11.34/2.03  --res_backward_subs_resolution          true
% 11.34/2.03  --res_orphan_elimination                true
% 11.34/2.03  --res_time_limit                        2.
% 11.34/2.03  --res_out_proof                         true
% 11.34/2.03  
% 11.34/2.03  ------ Superposition Options
% 11.34/2.03  
% 11.34/2.03  --superposition_flag                    true
% 11.34/2.03  --sup_passive_queue_type                priority_queues
% 11.34/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.34/2.03  --sup_passive_queues_freq               [8;1;4]
% 11.34/2.03  --demod_completeness_check              fast
% 11.34/2.03  --demod_use_ground                      true
% 11.34/2.03  --sup_to_prop_solver                    passive
% 11.34/2.03  --sup_prop_simpl_new                    true
% 11.34/2.03  --sup_prop_simpl_given                  true
% 11.34/2.03  --sup_fun_splitting                     true
% 11.34/2.03  --sup_smt_interval                      50000
% 11.34/2.03  
% 11.34/2.03  ------ Superposition Simplification Setup
% 11.34/2.03  
% 11.34/2.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.34/2.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.34/2.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.34/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.34/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.34/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.34/2.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.34/2.03  --sup_immed_triv                        [TrivRules]
% 11.34/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.03  --sup_immed_bw_main                     []
% 11.34/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.34/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.34/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.03  --sup_input_bw                          []
% 11.34/2.03  
% 11.34/2.03  ------ Combination Options
% 11.34/2.03  
% 11.34/2.03  --comb_res_mult                         3
% 11.34/2.03  --comb_sup_mult                         2
% 11.34/2.03  --comb_inst_mult                        10
% 11.34/2.03  
% 11.34/2.03  ------ Debug Options
% 11.34/2.03  
% 11.34/2.03  --dbg_backtrace                         false
% 11.34/2.03  --dbg_dump_prop_clauses                 false
% 11.34/2.03  --dbg_dump_prop_clauses_file            -
% 11.34/2.03  --dbg_out_stat                          false
% 11.34/2.03  ------ Parsing...
% 11.34/2.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.34/2.03  
% 11.34/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.34/2.03  
% 11.34/2.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.34/2.03  
% 11.34/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.34/2.03  ------ Proving...
% 11.34/2.03  ------ Problem Properties 
% 11.34/2.03  
% 11.34/2.03  
% 11.34/2.03  clauses                                 12
% 11.34/2.03  conjectures                             1
% 11.34/2.03  EPR                                     0
% 11.34/2.03  Horn                                    12
% 11.34/2.03  unary                                   11
% 11.34/2.03  binary                                  1
% 11.34/2.03  lits                                    13
% 11.34/2.03  lits eq                                 10
% 11.34/2.03  fd_pure                                 0
% 11.34/2.03  fd_pseudo                               0
% 11.34/2.03  fd_cond                                 0
% 11.34/2.03  fd_pseudo_cond                          0
% 11.34/2.03  AC symbols                              0
% 11.34/2.03  
% 11.34/2.03  ------ Schedule dynamic 5 is on 
% 11.34/2.03  
% 11.34/2.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.34/2.03  
% 11.34/2.03  
% 11.34/2.03  ------ 
% 11.34/2.03  Current options:
% 11.34/2.03  ------ 
% 11.34/2.03  
% 11.34/2.03  ------ Input Options
% 11.34/2.03  
% 11.34/2.03  --out_options                           all
% 11.34/2.03  --tptp_safe_out                         true
% 11.34/2.03  --problem_path                          ""
% 11.34/2.03  --include_path                          ""
% 11.34/2.03  --clausifier                            res/vclausify_rel
% 11.34/2.03  --clausifier_options                    ""
% 11.34/2.03  --stdin                                 false
% 11.34/2.03  --stats_out                             all
% 11.34/2.03  
% 11.34/2.03  ------ General Options
% 11.34/2.03  
% 11.34/2.03  --fof                                   false
% 11.34/2.03  --time_out_real                         305.
% 11.34/2.03  --time_out_virtual                      -1.
% 11.34/2.03  --symbol_type_check                     false
% 11.34/2.03  --clausify_out                          false
% 11.34/2.03  --sig_cnt_out                           false
% 11.34/2.03  --trig_cnt_out                          false
% 11.34/2.03  --trig_cnt_out_tolerance                1.
% 11.34/2.03  --trig_cnt_out_sk_spl                   false
% 11.34/2.03  --abstr_cl_out                          false
% 11.34/2.03  
% 11.34/2.03  ------ Global Options
% 11.34/2.03  
% 11.34/2.03  --schedule                              default
% 11.34/2.03  --add_important_lit                     false
% 11.34/2.03  --prop_solver_per_cl                    1000
% 11.34/2.03  --min_unsat_core                        false
% 11.34/2.03  --soft_assumptions                      false
% 11.34/2.03  --soft_lemma_size                       3
% 11.34/2.03  --prop_impl_unit_size                   0
% 11.34/2.03  --prop_impl_unit                        []
% 11.34/2.03  --share_sel_clauses                     true
% 11.34/2.03  --reset_solvers                         false
% 11.34/2.03  --bc_imp_inh                            [conj_cone]
% 11.34/2.03  --conj_cone_tolerance                   3.
% 11.34/2.03  --extra_neg_conj                        none
% 11.34/2.03  --large_theory_mode                     true
% 11.34/2.03  --prolific_symb_bound                   200
% 11.34/2.03  --lt_threshold                          2000
% 11.34/2.03  --clause_weak_htbl                      true
% 11.34/2.03  --gc_record_bc_elim                     false
% 11.34/2.03  
% 11.34/2.03  ------ Preprocessing Options
% 11.34/2.03  
% 11.34/2.03  --preprocessing_flag                    true
% 11.34/2.03  --time_out_prep_mult                    0.1
% 11.34/2.03  --splitting_mode                        input
% 11.34/2.03  --splitting_grd                         true
% 11.34/2.03  --splitting_cvd                         false
% 11.34/2.03  --splitting_cvd_svl                     false
% 11.34/2.03  --splitting_nvd                         32
% 11.34/2.03  --sub_typing                            true
% 11.34/2.03  --prep_gs_sim                           true
% 11.34/2.03  --prep_unflatten                        true
% 11.34/2.03  --prep_res_sim                          true
% 11.34/2.03  --prep_upred                            true
% 11.34/2.03  --prep_sem_filter                       exhaustive
% 11.34/2.03  --prep_sem_filter_out                   false
% 11.34/2.03  --pred_elim                             true
% 11.34/2.03  --res_sim_input                         true
% 11.34/2.03  --eq_ax_congr_red                       true
% 11.34/2.03  --pure_diseq_elim                       true
% 11.34/2.03  --brand_transform                       false
% 11.34/2.03  --non_eq_to_eq                          false
% 11.34/2.03  --prep_def_merge                        true
% 11.34/2.03  --prep_def_merge_prop_impl              false
% 11.34/2.03  --prep_def_merge_mbd                    true
% 11.34/2.03  --prep_def_merge_tr_red                 false
% 11.34/2.03  --prep_def_merge_tr_cl                  false
% 11.34/2.03  --smt_preprocessing                     true
% 11.34/2.03  --smt_ac_axioms                         fast
% 11.34/2.03  --preprocessed_out                      false
% 11.34/2.03  --preprocessed_stats                    false
% 11.34/2.03  
% 11.34/2.03  ------ Abstraction refinement Options
% 11.34/2.03  
% 11.34/2.03  --abstr_ref                             []
% 11.34/2.03  --abstr_ref_prep                        false
% 11.34/2.03  --abstr_ref_until_sat                   false
% 11.34/2.03  --abstr_ref_sig_restrict                funpre
% 11.34/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.34/2.03  --abstr_ref_under                       []
% 11.34/2.03  
% 11.34/2.03  ------ SAT Options
% 11.34/2.03  
% 11.34/2.03  --sat_mode                              false
% 11.34/2.03  --sat_fm_restart_options                ""
% 11.34/2.03  --sat_gr_def                            false
% 11.34/2.03  --sat_epr_types                         true
% 11.34/2.03  --sat_non_cyclic_types                  false
% 11.34/2.03  --sat_finite_models                     false
% 11.34/2.03  --sat_fm_lemmas                         false
% 11.34/2.03  --sat_fm_prep                           false
% 11.34/2.03  --sat_fm_uc_incr                        true
% 11.34/2.03  --sat_out_model                         small
% 11.34/2.03  --sat_out_clauses                       false
% 11.34/2.03  
% 11.34/2.03  ------ QBF Options
% 11.34/2.03  
% 11.34/2.03  --qbf_mode                              false
% 11.34/2.03  --qbf_elim_univ                         false
% 11.34/2.03  --qbf_dom_inst                          none
% 11.34/2.03  --qbf_dom_pre_inst                      false
% 11.34/2.03  --qbf_sk_in                             false
% 11.34/2.03  --qbf_pred_elim                         true
% 11.34/2.03  --qbf_split                             512
% 11.34/2.03  
% 11.34/2.03  ------ BMC1 Options
% 11.34/2.03  
% 11.34/2.03  --bmc1_incremental                      false
% 11.34/2.03  --bmc1_axioms                           reachable_all
% 11.34/2.03  --bmc1_min_bound                        0
% 11.34/2.03  --bmc1_max_bound                        -1
% 11.34/2.03  --bmc1_max_bound_default                -1
% 11.34/2.03  --bmc1_symbol_reachability              true
% 11.34/2.03  --bmc1_property_lemmas                  false
% 11.34/2.03  --bmc1_k_induction                      false
% 11.34/2.03  --bmc1_non_equiv_states                 false
% 11.34/2.03  --bmc1_deadlock                         false
% 11.34/2.03  --bmc1_ucm                              false
% 11.34/2.03  --bmc1_add_unsat_core                   none
% 11.34/2.03  --bmc1_unsat_core_children              false
% 11.34/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.34/2.03  --bmc1_out_stat                         full
% 11.34/2.03  --bmc1_ground_init                      false
% 11.34/2.03  --bmc1_pre_inst_next_state              false
% 11.34/2.03  --bmc1_pre_inst_state                   false
% 11.34/2.03  --bmc1_pre_inst_reach_state             false
% 11.34/2.03  --bmc1_out_unsat_core                   false
% 11.34/2.03  --bmc1_aig_witness_out                  false
% 11.34/2.03  --bmc1_verbose                          false
% 11.34/2.03  --bmc1_dump_clauses_tptp                false
% 11.34/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.34/2.03  --bmc1_dump_file                        -
% 11.34/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.34/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.34/2.03  --bmc1_ucm_extend_mode                  1
% 11.34/2.03  --bmc1_ucm_init_mode                    2
% 11.34/2.03  --bmc1_ucm_cone_mode                    none
% 11.34/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.34/2.03  --bmc1_ucm_relax_model                  4
% 11.34/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.34/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.34/2.03  --bmc1_ucm_layered_model                none
% 11.34/2.03  --bmc1_ucm_max_lemma_size               10
% 11.34/2.03  
% 11.34/2.03  ------ AIG Options
% 11.34/2.03  
% 11.34/2.03  --aig_mode                              false
% 11.34/2.03  
% 11.34/2.03  ------ Instantiation Options
% 11.34/2.03  
% 11.34/2.03  --instantiation_flag                    true
% 11.34/2.03  --inst_sos_flag                         true
% 11.34/2.03  --inst_sos_phase                        true
% 11.34/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.34/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.34/2.03  --inst_lit_sel_side                     none
% 11.34/2.03  --inst_solver_per_active                1400
% 11.34/2.03  --inst_solver_calls_frac                1.
% 11.34/2.03  --inst_passive_queue_type               priority_queues
% 11.34/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.34/2.03  --inst_passive_queues_freq              [25;2]
% 11.34/2.03  --inst_dismatching                      true
% 11.34/2.03  --inst_eager_unprocessed_to_passive     true
% 11.34/2.03  --inst_prop_sim_given                   true
% 11.34/2.03  --inst_prop_sim_new                     false
% 11.34/2.03  --inst_subs_new                         false
% 11.34/2.03  --inst_eq_res_simp                      false
% 11.34/2.03  --inst_subs_given                       false
% 11.34/2.03  --inst_orphan_elimination               true
% 11.34/2.03  --inst_learning_loop_flag               true
% 11.34/2.03  --inst_learning_start                   3000
% 11.34/2.03  --inst_learning_factor                  2
% 11.34/2.03  --inst_start_prop_sim_after_learn       3
% 11.34/2.03  --inst_sel_renew                        solver
% 11.34/2.03  --inst_lit_activity_flag                true
% 11.34/2.03  --inst_restr_to_given                   false
% 11.34/2.03  --inst_activity_threshold               500
% 11.34/2.03  --inst_out_proof                        true
% 11.34/2.03  
% 11.34/2.03  ------ Resolution Options
% 11.34/2.03  
% 11.34/2.03  --resolution_flag                       false
% 11.34/2.03  --res_lit_sel                           adaptive
% 11.34/2.03  --res_lit_sel_side                      none
% 11.34/2.03  --res_ordering                          kbo
% 11.34/2.03  --res_to_prop_solver                    active
% 11.34/2.03  --res_prop_simpl_new                    false
% 11.34/2.03  --res_prop_simpl_given                  true
% 11.34/2.03  --res_passive_queue_type                priority_queues
% 11.34/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.34/2.03  --res_passive_queues_freq               [15;5]
% 11.34/2.03  --res_forward_subs                      full
% 11.34/2.03  --res_backward_subs                     full
% 11.34/2.03  --res_forward_subs_resolution           true
% 11.34/2.03  --res_backward_subs_resolution          true
% 11.34/2.03  --res_orphan_elimination                true
% 11.34/2.03  --res_time_limit                        2.
% 11.34/2.03  --res_out_proof                         true
% 11.34/2.03  
% 11.34/2.03  ------ Superposition Options
% 11.34/2.03  
% 11.34/2.03  --superposition_flag                    true
% 11.34/2.03  --sup_passive_queue_type                priority_queues
% 11.34/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.34/2.03  --sup_passive_queues_freq               [8;1;4]
% 11.34/2.03  --demod_completeness_check              fast
% 11.34/2.03  --demod_use_ground                      true
% 11.34/2.03  --sup_to_prop_solver                    passive
% 11.34/2.03  --sup_prop_simpl_new                    true
% 11.34/2.03  --sup_prop_simpl_given                  true
% 11.34/2.03  --sup_fun_splitting                     true
% 11.34/2.03  --sup_smt_interval                      50000
% 11.34/2.03  
% 11.34/2.03  ------ Superposition Simplification Setup
% 11.34/2.03  
% 11.34/2.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.34/2.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.34/2.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.34/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.34/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.34/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.34/2.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.34/2.03  --sup_immed_triv                        [TrivRules]
% 11.34/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.03  --sup_immed_bw_main                     []
% 11.34/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.34/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.34/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.34/2.03  --sup_input_bw                          []
% 11.34/2.03  
% 11.34/2.03  ------ Combination Options
% 11.34/2.03  
% 11.34/2.03  --comb_res_mult                         3
% 11.34/2.03  --comb_sup_mult                         2
% 11.34/2.03  --comb_inst_mult                        10
% 11.34/2.03  
% 11.34/2.03  ------ Debug Options
% 11.34/2.03  
% 11.34/2.03  --dbg_backtrace                         false
% 11.34/2.03  --dbg_dump_prop_clauses                 false
% 11.34/2.03  --dbg_dump_prop_clauses_file            -
% 11.34/2.03  --dbg_out_stat                          false
% 11.34/2.03  
% 11.34/2.03  
% 11.34/2.03  
% 11.34/2.03  
% 11.34/2.03  ------ Proving...
% 11.34/2.03  
% 11.34/2.03  
% 11.34/2.03  % SZS status Theorem for theBenchmark.p
% 11.34/2.03  
% 11.34/2.03  % SZS output start CNFRefutation for theBenchmark.p
% 11.34/2.03  
% 11.34/2.03  fof(f11,axiom,(
% 11.34/2.03    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f31,plain,(
% 11.34/2.03    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.34/2.03    inference(cnf_transformation,[],[f11])).
% 11.34/2.03  
% 11.34/2.03  fof(f12,axiom,(
% 11.34/2.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f16,plain,(
% 11.34/2.03    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 11.34/2.03    inference(unused_predicate_definition_removal,[],[f12])).
% 11.34/2.03  
% 11.34/2.03  fof(f17,plain,(
% 11.34/2.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 11.34/2.03    inference(ennf_transformation,[],[f16])).
% 11.34/2.03  
% 11.34/2.03  fof(f32,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.34/2.03    inference(cnf_transformation,[],[f17])).
% 11.34/2.03  
% 11.34/2.03  fof(f7,axiom,(
% 11.34/2.03    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f27,plain,(
% 11.34/2.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.34/2.03    inference(cnf_transformation,[],[f7])).
% 11.34/2.03  
% 11.34/2.03  fof(f1,axiom,(
% 11.34/2.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f21,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.34/2.03    inference(cnf_transformation,[],[f1])).
% 11.34/2.03  
% 11.34/2.03  fof(f6,axiom,(
% 11.34/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f26,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.34/2.03    inference(cnf_transformation,[],[f6])).
% 11.34/2.03  
% 11.34/2.03  fof(f9,axiom,(
% 11.34/2.03    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f29,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 11.34/2.03    inference(cnf_transformation,[],[f9])).
% 11.34/2.03  
% 11.34/2.03  fof(f8,axiom,(
% 11.34/2.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f28,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.34/2.03    inference(cnf_transformation,[],[f8])).
% 11.34/2.03  
% 11.34/2.03  fof(f37,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 11.34/2.03    inference(definition_unfolding,[],[f29,f28])).
% 11.34/2.03  
% 11.34/2.03  fof(f2,axiom,(
% 11.34/2.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f22,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.34/2.03    inference(cnf_transformation,[],[f2])).
% 11.34/2.03  
% 11.34/2.03  fof(f35,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.34/2.03    inference(definition_unfolding,[],[f22,f28,f28])).
% 11.34/2.03  
% 11.34/2.03  fof(f5,axiom,(
% 11.34/2.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f25,plain,(
% 11.34/2.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.34/2.03    inference(cnf_transformation,[],[f5])).
% 11.34/2.03  
% 11.34/2.03  fof(f13,axiom,(
% 11.34/2.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f33,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 11.34/2.03    inference(cnf_transformation,[],[f13])).
% 11.34/2.03  
% 11.34/2.03  fof(f3,axiom,(
% 11.34/2.03    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f23,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 11.34/2.03    inference(cnf_transformation,[],[f3])).
% 11.34/2.03  
% 11.34/2.03  fof(f39,plain,(
% 11.34/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.34/2.03    inference(definition_unfolding,[],[f33,f23,f28])).
% 11.34/2.03  
% 11.34/2.03  fof(f4,axiom,(
% 11.34/2.03    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f24,plain,(
% 11.34/2.03    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 11.34/2.03    inference(cnf_transformation,[],[f4])).
% 11.34/2.03  
% 11.34/2.03  fof(f36,plain,(
% 11.34/2.03    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 11.34/2.03    inference(definition_unfolding,[],[f24,f28,f23])).
% 11.34/2.03  
% 11.34/2.03  fof(f14,conjecture,(
% 11.34/2.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.34/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.34/2.03  
% 11.34/2.03  fof(f15,negated_conjecture,(
% 11.34/2.03    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.34/2.03    inference(negated_conjecture,[],[f14])).
% 11.34/2.03  
% 11.34/2.03  fof(f18,plain,(
% 11.34/2.03    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.34/2.03    inference(ennf_transformation,[],[f15])).
% 11.34/2.03  
% 11.34/2.03  fof(f19,plain,(
% 11.34/2.03    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 11.34/2.03    introduced(choice_axiom,[])).
% 11.34/2.03  
% 11.34/2.03  fof(f20,plain,(
% 11.34/2.03    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 11.34/2.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 11.34/2.03  
% 11.34/2.03  fof(f34,plain,(
% 11.34/2.03    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 11.34/2.03    inference(cnf_transformation,[],[f20])).
% 11.34/2.03  
% 11.34/2.03  fof(f40,plain,(
% 11.34/2.03    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 11.34/2.03    inference(definition_unfolding,[],[f34,f23,f23,f28])).
% 11.34/2.03  
% 11.34/2.03  cnf(c_8,plain,
% 11.34/2.03      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.34/2.03      inference(cnf_transformation,[],[f31]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_135,plain,
% 11.34/2.03      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 11.34/2.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_9,plain,
% 11.34/2.03      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 11.34/2.03      inference(cnf_transformation,[],[f32]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_134,plain,
% 11.34/2.03      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 11.34/2.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_383,plain,
% 11.34/2.03      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_135,c_134]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_5,plain,
% 11.34/2.03      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.34/2.03      inference(cnf_transformation,[],[f27]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1774,plain,
% 11.34/2.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_383,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1788,plain,
% 11.34/2.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_1774,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_0,plain,
% 11.34/2.03      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.34/2.03      inference(cnf_transformation,[],[f21]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_4,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.34/2.03      inference(cnf_transformation,[],[f26]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_386,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_6,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 11.34/2.03      inference(cnf_transformation,[],[f37]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1142,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_386,c_6]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.34/2.03      inference(cnf_transformation,[],[f35]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1149,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_386,c_1]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_3,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.34/2.03      inference(cnf_transformation,[],[f25]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_389,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_390,plain,
% 11.34/2.03      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_389,c_3]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_564,plain,
% 11.34/2.03      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_0,c_390]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_609,plain,
% 11.34/2.03      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_564,c_4]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_550,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_3,c_6]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_741,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),X0) = X0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_609,c_550]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_829,plain,
% 11.34/2.03      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_741,c_6]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_833,plain,
% 11.34/2.03      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_829,c_609]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_939,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_833,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_942,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_939,c_829]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1152,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_1149,c_3,c_942]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_10,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 11.34/2.03      inference(cnf_transformation,[],[f39]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1147,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_386,c_10]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1155,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_1147,c_3,c_942]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1156,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k2_xboole_0(X1,X0)) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1155,c_564]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1158,plain,
% 11.34/2.03      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1142,c_1152,c_1156]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_41542,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1788,c_1158]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1353,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_0,c_942]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1508,plain,
% 11.34/2.03      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_6,c_1353]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1626,plain,
% 11.34/2.03      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_5,c_1508]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_7519,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1626,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_2058,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1,c_1158]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1635,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1508,c_10]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1660,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1635,c_5,c_564]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1661,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1660,c_6,c_390]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_2085,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_2058,c_1661]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_23164,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)),X2),k4_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_7519,c_2085]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1950,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X0,X1) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1152,c_6]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1966,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_1950,c_386]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_4288,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1353,c_1966]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1646,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1508,c_10]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1648,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1508,c_1]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1651,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1648,c_5,c_390]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1654,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1646,c_1651]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1655,plain,
% 11.34/2.03      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1654,c_6,c_390]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1944,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1152,c_1655]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_4175,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_0,c_1944]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_4334,plain,
% 11.34/2.03      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_4288,c_4175]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_5405,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1158,c_4334]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_5457,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_5405,c_4334]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_466,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_478,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_466,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_15952,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_2085,c_478]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_16080,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_15952,c_2085]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_23225,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_23164,c_3,c_5457,c_16080]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1144,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_386,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1157,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1144,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_36285,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1157,c_1158]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_467,plain,
% 11.34/2.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_477,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_467,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_13650,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_477,c_942]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_34895,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1)),k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_13650,c_2085]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_2060,plain,
% 11.34/2.03      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_4,c_1158]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_2084,plain,
% 11.34/2.03      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_2060,c_1158]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1919,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_0,c_1152]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_4458,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k2_xboole_0(X1,X0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_2084,c_1919]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_4484,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_4458,c_1353]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_34976,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X1)),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_34895,c_4484]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_554,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_7483,plain,
% 11.34/2.03      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k1_xboole_0)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1626,c_554]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_7561,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_7483,c_5,c_564]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_5413,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_4334,c_4175]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_2,plain,
% 11.34/2.03      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
% 11.34/2.03      inference(cnf_transformation,[],[f36]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_136,plain,
% 11.34/2.03      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = iProver_top ),
% 11.34/2.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1148,plain,
% 11.34/2.03      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = iProver_top ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_386,c_136]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1153,plain,
% 11.34/2.03      ( r1_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))) = iProver_top ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_1148,c_3,c_942]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1154,plain,
% 11.34/2.03      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1153,c_564]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1394,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1154,c_134]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1545,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_5,c_1394]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1808,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1,c_1661]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_3007,plain,
% 11.34/2.03      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1545,c_1808]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_4714,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_2084,c_3007]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_4750,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_4714,c_3007]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_5452,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_5413,c_4750]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_7562,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_7561,c_477,c_5452]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_30348,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_7562,c_1966]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_34977,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_34976,c_1157,c_30348]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_36381,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_36285,c_34977]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_41647,plain,
% 11.34/2.03      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.34/2.03      inference(light_normalisation,
% 11.34/2.03                [status(thm)],
% 11.34/2.03                [c_41542,c_23225,c_36381]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1942,plain,
% 11.34/2.03      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1152,c_1661]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_11,negated_conjecture,
% 11.34/2.03      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
% 11.34/2.03      inference(cnf_transformation,[],[f40]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_138,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) != k2_xboole_0(sK0,sK1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_11,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_223,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_0,c_138]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_3440,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_1942,c_223]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1105,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_10,c_4]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_3441,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_3440,c_1105]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1922,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_10,c_1152]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_974,plain,
% 11.34/2.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_136,c_134]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1984,plain,
% 11.34/2.03      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 11.34/2.03      inference(light_normalisation,[status(thm)],[c_1922,c_974]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_3442,plain,
% 11.34/2.03      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK0) != k2_xboole_0(sK0,sK1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_3441,c_1966,c_1984]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_58973,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k2_xboole_0(sK0,sK1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_41647,c_3442]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_1558,plain,
% 11.34/2.03      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1394,c_5]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_7273,plain,
% 11.34/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X2,X0),X1)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 11.34/2.03      inference(superposition,[status(thm)],[c_1558,c_5457]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_58977,plain,
% 11.34/2.03      ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK1) ),
% 11.34/2.03      inference(demodulation,[status(thm)],[c_58973,c_1661,c_7273]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(c_288,plain,
% 11.34/2.03      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK1) ),
% 11.34/2.03      inference(instantiation,[status(thm)],[c_0]) ).
% 11.34/2.03  
% 11.34/2.03  cnf(contradiction,plain,
% 11.34/2.03      ( $false ),
% 11.34/2.03      inference(minisat,[status(thm)],[c_58977,c_288]) ).
% 11.34/2.03  
% 11.34/2.03  
% 11.34/2.03  % SZS output end CNFRefutation for theBenchmark.p
% 11.34/2.03  
% 11.34/2.03  ------                               Statistics
% 11.34/2.03  
% 11.34/2.03  ------ General
% 11.34/2.03  
% 11.34/2.03  abstr_ref_over_cycles:                  0
% 11.34/2.03  abstr_ref_under_cycles:                 0
% 11.34/2.03  gc_basic_clause_elim:                   0
% 11.34/2.03  forced_gc_time:                         0
% 11.34/2.03  parsing_time:                           0.008
% 11.34/2.03  unif_index_cands_time:                  0.
% 11.34/2.03  unif_index_add_time:                    0.
% 11.34/2.03  orderings_time:                         0.
% 11.34/2.03  out_proof_time:                         0.015
% 11.34/2.03  total_time:                             1.446
% 11.34/2.03  num_of_symbols:                         41
% 11.34/2.03  num_of_terms:                           81395
% 11.34/2.03  
% 11.34/2.03  ------ Preprocessing
% 11.34/2.03  
% 11.34/2.03  num_of_splits:                          0
% 11.34/2.03  num_of_split_atoms:                     4
% 11.34/2.03  num_of_reused_defs:                     1
% 11.34/2.03  num_eq_ax_congr_red:                    0
% 11.34/2.03  num_of_sem_filtered_clauses:            1
% 11.34/2.03  num_of_subtypes:                        0
% 11.34/2.03  monotx_restored_types:                  0
% 11.34/2.03  sat_num_of_epr_types:                   0
% 11.34/2.03  sat_num_of_non_cyclic_types:            0
% 11.34/2.03  sat_guarded_non_collapsed_types:        0
% 11.34/2.03  num_pure_diseq_elim:                    0
% 11.34/2.03  simp_replaced_by:                       0
% 11.34/2.03  res_preprocessed:                       47
% 11.34/2.03  prep_upred:                             0
% 11.34/2.03  prep_unflattend:                        4
% 11.34/2.03  smt_new_axioms:                         0
% 11.34/2.03  pred_elim_cands:                        1
% 11.34/2.03  pred_elim:                              0
% 11.34/2.03  pred_elim_cl:                           0
% 11.34/2.03  pred_elim_cycles:                       1
% 11.34/2.03  merged_defs:                            0
% 11.34/2.03  merged_defs_ncl:                        0
% 11.34/2.03  bin_hyper_res:                          0
% 11.34/2.03  prep_cycles:                            3
% 11.34/2.03  pred_elim_time:                         0.
% 11.34/2.03  splitting_time:                         0.
% 11.34/2.03  sem_filter_time:                        0.
% 11.34/2.03  monotx_time:                            0.
% 11.34/2.03  subtype_inf_time:                       0.
% 11.34/2.03  
% 11.34/2.03  ------ Problem properties
% 11.34/2.03  
% 11.34/2.03  clauses:                                12
% 11.34/2.03  conjectures:                            1
% 11.34/2.03  epr:                                    0
% 11.34/2.03  horn:                                   12
% 11.34/2.03  ground:                                 1
% 11.34/2.03  unary:                                  11
% 11.34/2.03  binary:                                 1
% 11.34/2.03  lits:                                   13
% 11.34/2.03  lits_eq:                                10
% 11.34/2.03  fd_pure:                                0
% 11.34/2.03  fd_pseudo:                              0
% 11.34/2.03  fd_cond:                                0
% 11.34/2.03  fd_pseudo_cond:                         0
% 11.34/2.03  ac_symbols:                             0
% 11.34/2.03  
% 11.34/2.03  ------ Propositional Solver
% 11.34/2.03  
% 11.34/2.03  prop_solver_calls:                      29
% 11.34/2.03  prop_fast_solver_calls:                 401
% 11.34/2.03  smt_solver_calls:                       0
% 11.34/2.03  smt_fast_solver_calls:                  0
% 11.34/2.03  prop_num_of_clauses:                    11944
% 11.34/2.03  prop_preprocess_simplified:             13021
% 11.34/2.03  prop_fo_subsumed:                       0
% 11.34/2.03  prop_solver_time:                       0.
% 11.34/2.03  smt_solver_time:                        0.
% 11.34/2.03  smt_fast_solver_time:                   0.
% 11.34/2.03  prop_fast_solver_time:                  0.
% 11.34/2.03  prop_unsat_core_time:                   0.001
% 11.34/2.03  
% 11.34/2.03  ------ QBF
% 11.34/2.03  
% 11.34/2.03  qbf_q_res:                              0
% 11.34/2.03  qbf_num_tautologies:                    0
% 11.34/2.03  qbf_prep_cycles:                        0
% 11.34/2.03  
% 11.34/2.03  ------ BMC1
% 11.34/2.03  
% 11.34/2.03  bmc1_current_bound:                     -1
% 11.34/2.03  bmc1_last_solved_bound:                 -1
% 11.34/2.03  bmc1_unsat_core_size:                   -1
% 11.34/2.03  bmc1_unsat_core_parents_size:           -1
% 11.34/2.03  bmc1_merge_next_fun:                    0
% 11.34/2.03  bmc1_unsat_core_clauses_time:           0.
% 11.34/2.03  
% 11.34/2.03  ------ Instantiation
% 11.34/2.03  
% 11.34/2.03  inst_num_of_clauses:                    2921
% 11.34/2.03  inst_num_in_passive:                    1822
% 11.34/2.03  inst_num_in_active:                     974
% 11.34/2.03  inst_num_in_unprocessed:                125
% 11.34/2.03  inst_num_of_loops:                      1060
% 11.34/2.03  inst_num_of_learning_restarts:          0
% 11.34/2.03  inst_num_moves_active_passive:          83
% 11.34/2.03  inst_lit_activity:                      0
% 11.34/2.03  inst_lit_activity_moves:                0
% 11.34/2.03  inst_num_tautologies:                   0
% 11.34/2.03  inst_num_prop_implied:                  0
% 11.34/2.03  inst_num_existing_simplified:           0
% 11.34/2.03  inst_num_eq_res_simplified:             0
% 11.34/2.03  inst_num_child_elim:                    0
% 11.34/2.03  inst_num_of_dismatching_blockings:      1304
% 11.34/2.03  inst_num_of_non_proper_insts:           4176
% 11.34/2.03  inst_num_of_duplicates:                 0
% 11.34/2.03  inst_inst_num_from_inst_to_res:         0
% 11.34/2.03  inst_dismatching_checking_time:         0.
% 11.34/2.03  
% 11.34/2.03  ------ Resolution
% 11.34/2.03  
% 11.34/2.03  res_num_of_clauses:                     0
% 11.34/2.03  res_num_in_passive:                     0
% 11.34/2.03  res_num_in_active:                      0
% 11.34/2.03  res_num_of_loops:                       50
% 11.34/2.03  res_forward_subset_subsumed:            1316
% 11.34/2.03  res_backward_subset_subsumed:           2
% 11.34/2.03  res_forward_subsumed:                   0
% 11.34/2.03  res_backward_subsumed:                  0
% 11.34/2.03  res_forward_subsumption_resolution:     0
% 11.34/2.03  res_backward_subsumption_resolution:    0
% 11.34/2.03  res_clause_to_clause_subsumption:       92819
% 11.34/2.03  res_orphan_elimination:                 0
% 11.34/2.03  res_tautology_del:                      409
% 11.34/2.03  res_num_eq_res_simplified:              0
% 11.34/2.03  res_num_sel_changes:                    0
% 11.34/2.03  res_moves_from_active_to_pass:          0
% 11.34/2.03  
% 11.34/2.03  ------ Superposition
% 11.34/2.03  
% 11.34/2.03  sup_time_total:                         0.
% 11.34/2.03  sup_time_generating:                    0.
% 11.34/2.03  sup_time_sim_full:                      0.
% 11.34/2.03  sup_time_sim_immed:                     0.
% 11.34/2.03  
% 11.34/2.03  sup_num_of_clauses:                     3814
% 11.34/2.03  sup_num_in_active:                      163
% 11.34/2.03  sup_num_in_passive:                     3651
% 11.34/2.03  sup_num_of_loops:                       211
% 11.34/2.03  sup_fw_superposition:                   16873
% 11.34/2.03  sup_bw_superposition:                   13370
% 11.34/2.03  sup_immediate_simplified:               12930
% 11.34/2.03  sup_given_eliminated:                   6
% 11.34/2.03  comparisons_done:                       0
% 11.34/2.03  comparisons_avoided:                    0
% 11.34/2.03  
% 11.34/2.03  ------ Simplifications
% 11.34/2.03  
% 11.34/2.03  
% 11.34/2.03  sim_fw_subset_subsumed:                 0
% 11.34/2.03  sim_bw_subset_subsumed:                 0
% 11.34/2.03  sim_fw_subsumed:                        2507
% 11.34/2.03  sim_bw_subsumed:                        58
% 11.34/2.03  sim_fw_subsumption_res:                 0
% 11.34/2.03  sim_bw_subsumption_res:                 0
% 11.34/2.03  sim_tautology_del:                      0
% 11.34/2.03  sim_eq_tautology_del:                   3247
% 11.34/2.03  sim_eq_res_simp:                        0
% 11.34/2.03  sim_fw_demodulated:                     8488
% 11.34/2.03  sim_bw_demodulated:                     111
% 11.34/2.03  sim_light_normalised:                   5229
% 11.34/2.03  sim_joinable_taut:                      0
% 11.34/2.03  sim_joinable_simp:                      0
% 11.34/2.03  sim_ac_normalised:                      0
% 11.34/2.03  sim_smt_subsumption:                    0
% 11.34/2.03  
%------------------------------------------------------------------------------
