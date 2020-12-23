%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:08 EST 2020

% Result     : Theorem 23.84s
% Output     : CNFRefutation 23.84s
% Verified   : 
% Statistics : Number of formulae       :  174 (4174 expanded)
%              Number of clauses        :  127 (1882 expanded)
%              Number of leaves         :   18 (1094 expanded)
%              Depth                    :   29
%              Number of atoms          :  192 (4245 expanded)
%              Number of equality atoms :  160 (4155 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f83,f70])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f85,f85])).

fof(f28,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f22,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f29,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f59,f85,f70])).

fof(f23,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f24,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f76,f85])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f68,f85])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f31,conjecture,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f31])).

fof(f39,plain,(
    ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f32])).

fof(f48,plain,
    ( ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ~ r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f48])).

fof(f84,plain,(
    ~ r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_30,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_425,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(theory_normalisation,[status(thm)],[c_1,c_30,c_2])).

cnf(c_23,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_920,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_30,c_2])).

cnf(c_2335,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_23,c_920])).

cnf(c_31,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1313,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_31,c_30])).

cnf(c_1227,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_23,c_2])).

cnf(c_1319,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1313,c_1227])).

cnf(c_1802,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_2,c_1319])).

cnf(c_2393,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2335,c_1802])).

cnf(c_919,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_30,c_2])).

cnf(c_2600,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2393,c_919])).

cnf(c_2604,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = X2 ),
    inference(demodulation,[status(thm)],[c_2600,c_23])).

cnf(c_6882,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X1 ),
    inference(superposition,[status(thm)],[c_425,c_2604])).

cnf(c_19,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_0,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_426,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(theory_normalisation,[status(thm)],[c_0,c_30,c_2])).

cnf(c_6721,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_19,c_426])).

cnf(c_6796,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_6721,c_23,c_31])).

cnf(c_7069,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X1 ),
    inference(light_normalisation,[status(thm)],[c_6882,c_6796])).

cnf(c_1876,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1802,c_1802])).

cnf(c_921,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_30,c_2])).

cnf(c_2750,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_921,c_1319])).

cnf(c_2339,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_1802,c_920])).

cnf(c_1870,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_30,c_1802])).

cnf(c_6593,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,k5_xboole_0(X3,X0)) ),
    inference(superposition,[status(thm)],[c_2339,c_1870])).

cnf(c_7070,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_7069,c_1876,c_2750,c_6593,c_6796])).

cnf(c_2752,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = X2 ),
    inference(superposition,[status(thm)],[c_921,c_1802])).

cnf(c_11939,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X2),k5_xboole_0(X2,X0)) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_7070,c_2752])).

cnf(c_2227,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1876,c_30])).

cnf(c_4699,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
    inference(superposition,[status(thm)],[c_919,c_2227])).

cnf(c_1872,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_1319,c_1802])).

cnf(c_2141,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1872,c_30])).

cnf(c_4360,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_2141,c_2141])).

cnf(c_4838,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_4699,c_4360])).

cnf(c_2219,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_919,c_1876])).

cnf(c_6562,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X3)) = k5_xboole_0(X0,k5_xboole_0(X3,X1)) ),
    inference(superposition,[status(thm)],[c_2339,c_2219])).

cnf(c_11966,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_11939,c_2339,c_4838,c_6562])).

cnf(c_24,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_882,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6746,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_882])).

cnf(c_7134,plain,
    ( r1_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6746,c_6796])).

cnf(c_14691,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_7134])).

cnf(c_27,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_879,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_42583,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_14691,c_879])).

cnf(c_25,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_419,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_25,c_30,c_2])).

cnf(c_881,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_12328,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_881,c_6796])).

cnf(c_12329,plain,
    ( r1_tarski(X0,k5_xboole_0(k4_xboole_0(X0,X1),X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12328,c_2750])).

cnf(c_12333,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_12329])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_884,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12390,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12333,c_884])).

cnf(c_105680,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0))),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_42583,c_12390])).

cnf(c_18,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_420,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_18,c_30,c_2])).

cnf(c_1889,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k5_xboole_0(X1,X2),X3)))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_30,c_420])).

cnf(c_2748,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_921,c_1876])).

cnf(c_8821,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),X1) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_425,c_2748])).

cnf(c_9048,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),X1) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_8821,c_6796])).

cnf(c_9049,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_9048,c_1319,c_1876,c_2748,c_4838,c_6796])).

cnf(c_24741,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,X1),X0)))) = k4_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_920,c_9049])).

cnf(c_2388,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2335,c_1876])).

cnf(c_13,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_885,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6745,plain,
    ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_885])).

cnf(c_7135,plain,
    ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6745,c_6796])).

cnf(c_7136,plain,
    ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7135,c_2750])).

cnf(c_15026,plain,
    ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2388,c_7136])).

cnf(c_15079,plain,
    ( r1_tarski(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15026,c_23])).

cnf(c_17,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_15080,plain,
    ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15079,c_17])).

cnf(c_15404,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15080,c_884])).

cnf(c_16219,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_15404,c_6796])).

cnf(c_16262,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_16219,c_15404])).

cnf(c_16263,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_16262,c_2388])).

cnf(c_1904,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_420,c_885])).

cnf(c_11275,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1904,c_884])).

cnf(c_16716,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16263,c_11275])).

cnf(c_1806,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_30,c_1319])).

cnf(c_3133,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_2393,c_1806])).

cnf(c_3181,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_3133,c_23])).

cnf(c_7325,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_425,c_3181])).

cnf(c_7534,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1)))),X0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_7325,c_6796])).

cnf(c_5630,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X2) = k5_xboole_0(X0,k5_xboole_0(X3,X1)) ),
    inference(superposition,[status(thm)],[c_921,c_2219])).

cnf(c_7535,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k4_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_7534,c_1876,c_2750,c_4838,c_5630,c_6796])).

cnf(c_18285,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_12390,c_7535])).

cnf(c_11936,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7070,c_2604])).

cnf(c_18515,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_18285,c_11936])).

cnf(c_18516,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_18515,c_1227])).

cnf(c_59207,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k5_xboole_0(X1,X0),X2)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_16716,c_18516])).

cnf(c_2351,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X0)) = X2 ),
    inference(superposition,[status(thm)],[c_920,c_1872])).

cnf(c_7921,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X1))))),k5_xboole_0(X1,X0)) = k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_425,c_2351])).

cnf(c_2350,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_920,c_1876])).

cnf(c_2338,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1876,c_920])).

cnf(c_2361,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_2338,c_30])).

cnf(c_7767,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X1,X0)) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_2350,c_2361])).

cnf(c_8139,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_7921,c_1319,c_2351,c_6796,c_7767])).

cnf(c_51097,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X0),X2),k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_16716,c_8139])).

cnf(c_2555,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30,c_2393])).

cnf(c_2234,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1876,c_919])).

cnf(c_23178,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3) ),
    inference(superposition,[status(thm)],[c_2555,c_2234])).

cnf(c_2500,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_30,c_2388])).

cnf(c_22379,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_2,c_2500])).

cnf(c_23202,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_23178,c_2388,c_4838,c_22379])).

cnf(c_51208,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X0),X2))) ),
    inference(demodulation,[status(thm)],[c_51097,c_23,c_4838,c_23202])).

cnf(c_59553,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X1),X2))) ),
    inference(light_normalisation,[status(thm)],[c_59207,c_2388,c_51208])).

cnf(c_83020,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_1889,c_24741,c_59553])).

cnf(c_83150,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X4,k5_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X3))),X4) ),
    inference(superposition,[status(thm)],[c_2141,c_83020])).

cnf(c_83735,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X4,k5_xboole_0(X1,X3)))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X3,X1)),X4) ),
    inference(demodulation,[status(thm)],[c_83150,c_2339,c_23202])).

cnf(c_83736,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,X3)),X3))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X3,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_83735,c_2361,c_4838])).

cnf(c_106011,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_105680,c_4838,c_83736])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_883,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_106618,plain,
    ( r1_tarski(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_106011,c_883])).

cnf(c_108982,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11966,c_106618])).

cnf(c_1894,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_19,c_420])).

cnf(c_1935,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1894,c_23,c_31])).

cnf(c_108992,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_108982,c_1935])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_876,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_115254,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_108992,c_876])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 23.84/3.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.84/3.51  
% 23.84/3.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.84/3.51  
% 23.84/3.51  ------  iProver source info
% 23.84/3.51  
% 23.84/3.51  git: date: 2020-06-30 10:37:57 +0100
% 23.84/3.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.84/3.51  git: non_committed_changes: false
% 23.84/3.51  git: last_make_outside_of_git: false
% 23.84/3.51  
% 23.84/3.51  ------ 
% 23.84/3.51  
% 23.84/3.51  ------ Input Options
% 23.84/3.51  
% 23.84/3.51  --out_options                           all
% 23.84/3.51  --tptp_safe_out                         true
% 23.84/3.51  --problem_path                          ""
% 23.84/3.51  --include_path                          ""
% 23.84/3.51  --clausifier                            res/vclausify_rel
% 23.84/3.51  --clausifier_options                    ""
% 23.84/3.51  --stdin                                 false
% 23.84/3.51  --stats_out                             all
% 23.84/3.51  
% 23.84/3.51  ------ General Options
% 23.84/3.51  
% 23.84/3.51  --fof                                   false
% 23.84/3.51  --time_out_real                         305.
% 23.84/3.51  --time_out_virtual                      -1.
% 23.84/3.51  --symbol_type_check                     false
% 23.84/3.51  --clausify_out                          false
% 23.84/3.51  --sig_cnt_out                           false
% 23.84/3.51  --trig_cnt_out                          false
% 23.84/3.51  --trig_cnt_out_tolerance                1.
% 23.84/3.51  --trig_cnt_out_sk_spl                   false
% 23.84/3.51  --abstr_cl_out                          false
% 23.84/3.51  
% 23.84/3.51  ------ Global Options
% 23.84/3.51  
% 23.84/3.51  --schedule                              default
% 23.84/3.51  --add_important_lit                     false
% 23.84/3.51  --prop_solver_per_cl                    1000
% 23.84/3.51  --min_unsat_core                        false
% 23.84/3.51  --soft_assumptions                      false
% 23.84/3.51  --soft_lemma_size                       3
% 23.84/3.51  --prop_impl_unit_size                   0
% 23.84/3.51  --prop_impl_unit                        []
% 23.84/3.51  --share_sel_clauses                     true
% 23.84/3.51  --reset_solvers                         false
% 23.84/3.51  --bc_imp_inh                            [conj_cone]
% 23.84/3.51  --conj_cone_tolerance                   3.
% 23.84/3.51  --extra_neg_conj                        none
% 23.84/3.51  --large_theory_mode                     true
% 23.84/3.51  --prolific_symb_bound                   200
% 23.84/3.51  --lt_threshold                          2000
% 23.84/3.51  --clause_weak_htbl                      true
% 23.84/3.51  --gc_record_bc_elim                     false
% 23.84/3.51  
% 23.84/3.51  ------ Preprocessing Options
% 23.84/3.51  
% 23.84/3.51  --preprocessing_flag                    true
% 23.84/3.51  --time_out_prep_mult                    0.1
% 23.84/3.51  --splitting_mode                        input
% 23.84/3.51  --splitting_grd                         true
% 23.84/3.51  --splitting_cvd                         false
% 23.84/3.51  --splitting_cvd_svl                     false
% 23.84/3.51  --splitting_nvd                         32
% 23.84/3.51  --sub_typing                            true
% 23.84/3.51  --prep_gs_sim                           true
% 23.84/3.51  --prep_unflatten                        true
% 23.84/3.51  --prep_res_sim                          true
% 23.84/3.51  --prep_upred                            true
% 23.84/3.51  --prep_sem_filter                       exhaustive
% 23.84/3.51  --prep_sem_filter_out                   false
% 23.84/3.51  --pred_elim                             true
% 23.84/3.51  --res_sim_input                         true
% 23.84/3.51  --eq_ax_congr_red                       true
% 23.84/3.51  --pure_diseq_elim                       true
% 23.84/3.51  --brand_transform                       false
% 23.84/3.51  --non_eq_to_eq                          false
% 23.84/3.51  --prep_def_merge                        true
% 23.84/3.51  --prep_def_merge_prop_impl              false
% 23.84/3.51  --prep_def_merge_mbd                    true
% 23.84/3.51  --prep_def_merge_tr_red                 false
% 23.84/3.51  --prep_def_merge_tr_cl                  false
% 23.84/3.51  --smt_preprocessing                     true
% 23.84/3.51  --smt_ac_axioms                         fast
% 23.84/3.51  --preprocessed_out                      false
% 23.84/3.51  --preprocessed_stats                    false
% 23.84/3.51  
% 23.84/3.51  ------ Abstraction refinement Options
% 23.84/3.51  
% 23.84/3.51  --abstr_ref                             []
% 23.84/3.51  --abstr_ref_prep                        false
% 23.84/3.51  --abstr_ref_until_sat                   false
% 23.84/3.51  --abstr_ref_sig_restrict                funpre
% 23.84/3.51  --abstr_ref_af_restrict_to_split_sk     false
% 23.84/3.51  --abstr_ref_under                       []
% 23.84/3.51  
% 23.84/3.51  ------ SAT Options
% 23.84/3.51  
% 23.84/3.51  --sat_mode                              false
% 23.84/3.51  --sat_fm_restart_options                ""
% 23.84/3.51  --sat_gr_def                            false
% 23.84/3.51  --sat_epr_types                         true
% 23.84/3.51  --sat_non_cyclic_types                  false
% 23.84/3.51  --sat_finite_models                     false
% 23.84/3.51  --sat_fm_lemmas                         false
% 23.84/3.51  --sat_fm_prep                           false
% 23.84/3.51  --sat_fm_uc_incr                        true
% 23.84/3.51  --sat_out_model                         small
% 23.84/3.51  --sat_out_clauses                       false
% 23.84/3.51  
% 23.84/3.51  ------ QBF Options
% 23.84/3.51  
% 23.84/3.51  --qbf_mode                              false
% 23.84/3.51  --qbf_elim_univ                         false
% 23.84/3.51  --qbf_dom_inst                          none
% 23.84/3.51  --qbf_dom_pre_inst                      false
% 23.84/3.51  --qbf_sk_in                             false
% 23.84/3.51  --qbf_pred_elim                         true
% 23.84/3.51  --qbf_split                             512
% 23.84/3.51  
% 23.84/3.51  ------ BMC1 Options
% 23.84/3.51  
% 23.84/3.51  --bmc1_incremental                      false
% 23.84/3.51  --bmc1_axioms                           reachable_all
% 23.84/3.51  --bmc1_min_bound                        0
% 23.84/3.51  --bmc1_max_bound                        -1
% 23.84/3.51  --bmc1_max_bound_default                -1
% 23.84/3.51  --bmc1_symbol_reachability              true
% 23.84/3.51  --bmc1_property_lemmas                  false
% 23.84/3.51  --bmc1_k_induction                      false
% 23.84/3.51  --bmc1_non_equiv_states                 false
% 23.84/3.51  --bmc1_deadlock                         false
% 23.84/3.51  --bmc1_ucm                              false
% 23.84/3.51  --bmc1_add_unsat_core                   none
% 23.84/3.51  --bmc1_unsat_core_children              false
% 23.84/3.51  --bmc1_unsat_core_extrapolate_axioms    false
% 23.84/3.51  --bmc1_out_stat                         full
% 23.84/3.51  --bmc1_ground_init                      false
% 23.84/3.51  --bmc1_pre_inst_next_state              false
% 23.84/3.51  --bmc1_pre_inst_state                   false
% 23.84/3.51  --bmc1_pre_inst_reach_state             false
% 23.84/3.51  --bmc1_out_unsat_core                   false
% 23.84/3.51  --bmc1_aig_witness_out                  false
% 23.84/3.51  --bmc1_verbose                          false
% 23.84/3.51  --bmc1_dump_clauses_tptp                false
% 23.84/3.51  --bmc1_dump_unsat_core_tptp             false
% 23.84/3.51  --bmc1_dump_file                        -
% 23.84/3.51  --bmc1_ucm_expand_uc_limit              128
% 23.84/3.51  --bmc1_ucm_n_expand_iterations          6
% 23.84/3.51  --bmc1_ucm_extend_mode                  1
% 23.84/3.51  --bmc1_ucm_init_mode                    2
% 23.84/3.51  --bmc1_ucm_cone_mode                    none
% 23.84/3.51  --bmc1_ucm_reduced_relation_type        0
% 23.84/3.51  --bmc1_ucm_relax_model                  4
% 23.84/3.51  --bmc1_ucm_full_tr_after_sat            true
% 23.84/3.51  --bmc1_ucm_expand_neg_assumptions       false
% 23.84/3.51  --bmc1_ucm_layered_model                none
% 23.84/3.51  --bmc1_ucm_max_lemma_size               10
% 23.84/3.51  
% 23.84/3.51  ------ AIG Options
% 23.84/3.51  
% 23.84/3.51  --aig_mode                              false
% 23.84/3.51  
% 23.84/3.51  ------ Instantiation Options
% 23.84/3.51  
% 23.84/3.51  --instantiation_flag                    true
% 23.84/3.51  --inst_sos_flag                         true
% 23.84/3.51  --inst_sos_phase                        true
% 23.84/3.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.84/3.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.84/3.51  --inst_lit_sel_side                     num_symb
% 23.84/3.51  --inst_solver_per_active                1400
% 23.84/3.51  --inst_solver_calls_frac                1.
% 23.84/3.51  --inst_passive_queue_type               priority_queues
% 23.84/3.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.84/3.51  --inst_passive_queues_freq              [25;2]
% 23.84/3.51  --inst_dismatching                      true
% 23.84/3.51  --inst_eager_unprocessed_to_passive     true
% 23.84/3.51  --inst_prop_sim_given                   true
% 23.84/3.51  --inst_prop_sim_new                     false
% 23.84/3.51  --inst_subs_new                         false
% 23.84/3.51  --inst_eq_res_simp                      false
% 23.84/3.51  --inst_subs_given                       false
% 23.84/3.51  --inst_orphan_elimination               true
% 23.84/3.51  --inst_learning_loop_flag               true
% 23.84/3.51  --inst_learning_start                   3000
% 23.84/3.51  --inst_learning_factor                  2
% 23.84/3.51  --inst_start_prop_sim_after_learn       3
% 23.84/3.51  --inst_sel_renew                        solver
% 23.84/3.51  --inst_lit_activity_flag                true
% 23.84/3.51  --inst_restr_to_given                   false
% 23.84/3.51  --inst_activity_threshold               500
% 23.84/3.51  --inst_out_proof                        true
% 23.84/3.51  
% 23.84/3.51  ------ Resolution Options
% 23.84/3.51  
% 23.84/3.51  --resolution_flag                       true
% 23.84/3.51  --res_lit_sel                           adaptive
% 23.84/3.51  --res_lit_sel_side                      none
% 23.84/3.51  --res_ordering                          kbo
% 23.84/3.51  --res_to_prop_solver                    active
% 23.84/3.51  --res_prop_simpl_new                    false
% 23.84/3.51  --res_prop_simpl_given                  true
% 23.84/3.51  --res_passive_queue_type                priority_queues
% 23.84/3.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.84/3.51  --res_passive_queues_freq               [15;5]
% 23.84/3.51  --res_forward_subs                      full
% 23.84/3.51  --res_backward_subs                     full
% 23.84/3.51  --res_forward_subs_resolution           true
% 23.84/3.51  --res_backward_subs_resolution          true
% 23.84/3.51  --res_orphan_elimination                true
% 23.84/3.51  --res_time_limit                        2.
% 23.84/3.51  --res_out_proof                         true
% 23.84/3.51  
% 23.84/3.51  ------ Superposition Options
% 23.84/3.51  
% 23.84/3.51  --superposition_flag                    true
% 23.84/3.51  --sup_passive_queue_type                priority_queues
% 23.84/3.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.84/3.51  --sup_passive_queues_freq               [8;1;4]
% 23.84/3.51  --demod_completeness_check              fast
% 23.84/3.51  --demod_use_ground                      true
% 23.84/3.51  --sup_to_prop_solver                    passive
% 23.84/3.51  --sup_prop_simpl_new                    true
% 23.84/3.51  --sup_prop_simpl_given                  true
% 23.84/3.51  --sup_fun_splitting                     true
% 23.84/3.51  --sup_smt_interval                      50000
% 23.84/3.51  
% 23.84/3.51  ------ Superposition Simplification Setup
% 23.84/3.51  
% 23.84/3.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.84/3.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.84/3.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.84/3.51  --sup_full_triv                         [TrivRules;PropSubs]
% 23.84/3.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.84/3.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.84/3.51  --sup_immed_triv                        [TrivRules]
% 23.84/3.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.51  --sup_immed_bw_main                     []
% 23.84/3.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.84/3.51  --sup_input_triv                        [Unflattening;TrivRules]
% 23.84/3.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.51  --sup_input_bw                          []
% 23.84/3.51  
% 23.84/3.51  ------ Combination Options
% 23.84/3.51  
% 23.84/3.51  --comb_res_mult                         3
% 23.84/3.51  --comb_sup_mult                         2
% 23.84/3.51  --comb_inst_mult                        10
% 23.84/3.51  
% 23.84/3.51  ------ Debug Options
% 23.84/3.51  
% 23.84/3.51  --dbg_backtrace                         false
% 23.84/3.51  --dbg_dump_prop_clauses                 false
% 23.84/3.51  --dbg_dump_prop_clauses_file            -
% 23.84/3.51  --dbg_out_stat                          false
% 23.84/3.51  ------ Parsing...
% 23.84/3.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.84/3.51  
% 23.84/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.84/3.51  
% 23.84/3.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.84/3.51  
% 23.84/3.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.84/3.51  ------ Proving...
% 23.84/3.51  ------ Problem Properties 
% 23.84/3.51  
% 23.84/3.51  
% 23.84/3.51  clauses                                 33
% 23.84/3.51  conjectures                             1
% 23.84/3.51  EPR                                     4
% 23.84/3.51  Horn                                    31
% 23.84/3.51  unary                                   22
% 23.84/3.51  binary                                  10
% 23.84/3.51  lits                                    45
% 23.84/3.51  lits eq                                 21
% 23.84/3.51  fd_pure                                 0
% 23.84/3.51  fd_pseudo                               0
% 23.84/3.51  fd_cond                                 0
% 23.84/3.51  fd_pseudo_cond                          1
% 23.84/3.51  AC symbols                              1
% 23.84/3.51  
% 23.84/3.51  ------ Schedule dynamic 5 is on 
% 23.84/3.51  
% 23.84/3.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.84/3.51  
% 23.84/3.51  
% 23.84/3.51  ------ 
% 23.84/3.51  Current options:
% 23.84/3.51  ------ 
% 23.84/3.51  
% 23.84/3.51  ------ Input Options
% 23.84/3.51  
% 23.84/3.51  --out_options                           all
% 23.84/3.51  --tptp_safe_out                         true
% 23.84/3.51  --problem_path                          ""
% 23.84/3.51  --include_path                          ""
% 23.84/3.51  --clausifier                            res/vclausify_rel
% 23.84/3.51  --clausifier_options                    ""
% 23.84/3.51  --stdin                                 false
% 23.84/3.51  --stats_out                             all
% 23.84/3.51  
% 23.84/3.51  ------ General Options
% 23.84/3.51  
% 23.84/3.51  --fof                                   false
% 23.84/3.51  --time_out_real                         305.
% 23.84/3.51  --time_out_virtual                      -1.
% 23.84/3.51  --symbol_type_check                     false
% 23.84/3.51  --clausify_out                          false
% 23.84/3.51  --sig_cnt_out                           false
% 23.84/3.51  --trig_cnt_out                          false
% 23.84/3.51  --trig_cnt_out_tolerance                1.
% 23.84/3.51  --trig_cnt_out_sk_spl                   false
% 23.84/3.51  --abstr_cl_out                          false
% 23.84/3.51  
% 23.84/3.51  ------ Global Options
% 23.84/3.51  
% 23.84/3.51  --schedule                              default
% 23.84/3.51  --add_important_lit                     false
% 23.84/3.51  --prop_solver_per_cl                    1000
% 23.84/3.51  --min_unsat_core                        false
% 23.84/3.51  --soft_assumptions                      false
% 23.84/3.51  --soft_lemma_size                       3
% 23.84/3.51  --prop_impl_unit_size                   0
% 23.84/3.51  --prop_impl_unit                        []
% 23.84/3.51  --share_sel_clauses                     true
% 23.84/3.51  --reset_solvers                         false
% 23.84/3.51  --bc_imp_inh                            [conj_cone]
% 23.84/3.51  --conj_cone_tolerance                   3.
% 23.84/3.51  --extra_neg_conj                        none
% 23.84/3.51  --large_theory_mode                     true
% 23.84/3.51  --prolific_symb_bound                   200
% 23.84/3.51  --lt_threshold                          2000
% 23.84/3.51  --clause_weak_htbl                      true
% 23.84/3.51  --gc_record_bc_elim                     false
% 23.84/3.51  
% 23.84/3.51  ------ Preprocessing Options
% 23.84/3.51  
% 23.84/3.51  --preprocessing_flag                    true
% 23.84/3.51  --time_out_prep_mult                    0.1
% 23.84/3.51  --splitting_mode                        input
% 23.84/3.51  --splitting_grd                         true
% 23.84/3.51  --splitting_cvd                         false
% 23.84/3.51  --splitting_cvd_svl                     false
% 23.84/3.51  --splitting_nvd                         32
% 23.84/3.51  --sub_typing                            true
% 23.84/3.51  --prep_gs_sim                           true
% 23.84/3.51  --prep_unflatten                        true
% 23.84/3.51  --prep_res_sim                          true
% 23.84/3.51  --prep_upred                            true
% 23.84/3.51  --prep_sem_filter                       exhaustive
% 23.84/3.51  --prep_sem_filter_out                   false
% 23.84/3.51  --pred_elim                             true
% 23.84/3.51  --res_sim_input                         true
% 23.84/3.51  --eq_ax_congr_red                       true
% 23.84/3.51  --pure_diseq_elim                       true
% 23.84/3.51  --brand_transform                       false
% 23.84/3.51  --non_eq_to_eq                          false
% 23.84/3.51  --prep_def_merge                        true
% 23.84/3.51  --prep_def_merge_prop_impl              false
% 23.84/3.51  --prep_def_merge_mbd                    true
% 23.84/3.51  --prep_def_merge_tr_red                 false
% 23.84/3.51  --prep_def_merge_tr_cl                  false
% 23.84/3.51  --smt_preprocessing                     true
% 23.84/3.51  --smt_ac_axioms                         fast
% 23.84/3.51  --preprocessed_out                      false
% 23.84/3.51  --preprocessed_stats                    false
% 23.84/3.51  
% 23.84/3.51  ------ Abstraction refinement Options
% 23.84/3.51  
% 23.84/3.51  --abstr_ref                             []
% 23.84/3.51  --abstr_ref_prep                        false
% 23.84/3.51  --abstr_ref_until_sat                   false
% 23.84/3.51  --abstr_ref_sig_restrict                funpre
% 23.84/3.51  --abstr_ref_af_restrict_to_split_sk     false
% 23.84/3.51  --abstr_ref_under                       []
% 23.84/3.51  
% 23.84/3.51  ------ SAT Options
% 23.84/3.51  
% 23.84/3.51  --sat_mode                              false
% 23.84/3.51  --sat_fm_restart_options                ""
% 23.84/3.51  --sat_gr_def                            false
% 23.84/3.51  --sat_epr_types                         true
% 23.84/3.51  --sat_non_cyclic_types                  false
% 23.84/3.51  --sat_finite_models                     false
% 23.84/3.51  --sat_fm_lemmas                         false
% 23.84/3.51  --sat_fm_prep                           false
% 23.84/3.51  --sat_fm_uc_incr                        true
% 23.84/3.51  --sat_out_model                         small
% 23.84/3.51  --sat_out_clauses                       false
% 23.84/3.51  
% 23.84/3.51  ------ QBF Options
% 23.84/3.51  
% 23.84/3.51  --qbf_mode                              false
% 23.84/3.51  --qbf_elim_univ                         false
% 23.84/3.51  --qbf_dom_inst                          none
% 23.84/3.51  --qbf_dom_pre_inst                      false
% 23.84/3.51  --qbf_sk_in                             false
% 23.84/3.51  --qbf_pred_elim                         true
% 23.84/3.51  --qbf_split                             512
% 23.84/3.51  
% 23.84/3.51  ------ BMC1 Options
% 23.84/3.51  
% 23.84/3.51  --bmc1_incremental                      false
% 23.84/3.51  --bmc1_axioms                           reachable_all
% 23.84/3.51  --bmc1_min_bound                        0
% 23.84/3.51  --bmc1_max_bound                        -1
% 23.84/3.51  --bmc1_max_bound_default                -1
% 23.84/3.51  --bmc1_symbol_reachability              true
% 23.84/3.51  --bmc1_property_lemmas                  false
% 23.84/3.51  --bmc1_k_induction                      false
% 23.84/3.51  --bmc1_non_equiv_states                 false
% 23.84/3.51  --bmc1_deadlock                         false
% 23.84/3.51  --bmc1_ucm                              false
% 23.84/3.51  --bmc1_add_unsat_core                   none
% 23.84/3.51  --bmc1_unsat_core_children              false
% 23.84/3.51  --bmc1_unsat_core_extrapolate_axioms    false
% 23.84/3.51  --bmc1_out_stat                         full
% 23.84/3.51  --bmc1_ground_init                      false
% 23.84/3.51  --bmc1_pre_inst_next_state              false
% 23.84/3.51  --bmc1_pre_inst_state                   false
% 23.84/3.51  --bmc1_pre_inst_reach_state             false
% 23.84/3.51  --bmc1_out_unsat_core                   false
% 23.84/3.51  --bmc1_aig_witness_out                  false
% 23.84/3.51  --bmc1_verbose                          false
% 23.84/3.51  --bmc1_dump_clauses_tptp                false
% 23.84/3.51  --bmc1_dump_unsat_core_tptp             false
% 23.84/3.51  --bmc1_dump_file                        -
% 23.84/3.51  --bmc1_ucm_expand_uc_limit              128
% 23.84/3.51  --bmc1_ucm_n_expand_iterations          6
% 23.84/3.51  --bmc1_ucm_extend_mode                  1
% 23.84/3.51  --bmc1_ucm_init_mode                    2
% 23.84/3.51  --bmc1_ucm_cone_mode                    none
% 23.84/3.51  --bmc1_ucm_reduced_relation_type        0
% 23.84/3.51  --bmc1_ucm_relax_model                  4
% 23.84/3.51  --bmc1_ucm_full_tr_after_sat            true
% 23.84/3.51  --bmc1_ucm_expand_neg_assumptions       false
% 23.84/3.51  --bmc1_ucm_layered_model                none
% 23.84/3.51  --bmc1_ucm_max_lemma_size               10
% 23.84/3.51  
% 23.84/3.51  ------ AIG Options
% 23.84/3.51  
% 23.84/3.51  --aig_mode                              false
% 23.84/3.51  
% 23.84/3.51  ------ Instantiation Options
% 23.84/3.51  
% 23.84/3.51  --instantiation_flag                    true
% 23.84/3.51  --inst_sos_flag                         true
% 23.84/3.51  --inst_sos_phase                        true
% 23.84/3.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.84/3.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.84/3.51  --inst_lit_sel_side                     none
% 23.84/3.51  --inst_solver_per_active                1400
% 23.84/3.51  --inst_solver_calls_frac                1.
% 23.84/3.51  --inst_passive_queue_type               priority_queues
% 23.84/3.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.84/3.51  --inst_passive_queues_freq              [25;2]
% 23.84/3.51  --inst_dismatching                      true
% 23.84/3.51  --inst_eager_unprocessed_to_passive     true
% 23.84/3.51  --inst_prop_sim_given                   true
% 23.84/3.51  --inst_prop_sim_new                     false
% 23.84/3.51  --inst_subs_new                         false
% 23.84/3.51  --inst_eq_res_simp                      false
% 23.84/3.51  --inst_subs_given                       false
% 23.84/3.51  --inst_orphan_elimination               true
% 23.84/3.51  --inst_learning_loop_flag               true
% 23.84/3.51  --inst_learning_start                   3000
% 23.84/3.51  --inst_learning_factor                  2
% 23.84/3.51  --inst_start_prop_sim_after_learn       3
% 23.84/3.51  --inst_sel_renew                        solver
% 23.84/3.51  --inst_lit_activity_flag                true
% 23.84/3.51  --inst_restr_to_given                   false
% 23.84/3.51  --inst_activity_threshold               500
% 23.84/3.51  --inst_out_proof                        true
% 23.84/3.51  
% 23.84/3.51  ------ Resolution Options
% 23.84/3.51  
% 23.84/3.51  --resolution_flag                       false
% 23.84/3.51  --res_lit_sel                           adaptive
% 23.84/3.51  --res_lit_sel_side                      none
% 23.84/3.51  --res_ordering                          kbo
% 23.84/3.51  --res_to_prop_solver                    active
% 23.84/3.51  --res_prop_simpl_new                    false
% 23.84/3.51  --res_prop_simpl_given                  true
% 23.84/3.51  --res_passive_queue_type                priority_queues
% 23.84/3.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.84/3.51  --res_passive_queues_freq               [15;5]
% 23.84/3.51  --res_forward_subs                      full
% 23.84/3.51  --res_backward_subs                     full
% 23.84/3.51  --res_forward_subs_resolution           true
% 23.84/3.51  --res_backward_subs_resolution          true
% 23.84/3.51  --res_orphan_elimination                true
% 23.84/3.51  --res_time_limit                        2.
% 23.84/3.51  --res_out_proof                         true
% 23.84/3.51  
% 23.84/3.51  ------ Superposition Options
% 23.84/3.51  
% 23.84/3.51  --superposition_flag                    true
% 23.84/3.51  --sup_passive_queue_type                priority_queues
% 23.84/3.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.84/3.51  --sup_passive_queues_freq               [8;1;4]
% 23.84/3.51  --demod_completeness_check              fast
% 23.84/3.51  --demod_use_ground                      true
% 23.84/3.51  --sup_to_prop_solver                    passive
% 23.84/3.51  --sup_prop_simpl_new                    true
% 23.84/3.51  --sup_prop_simpl_given                  true
% 23.84/3.51  --sup_fun_splitting                     true
% 23.84/3.51  --sup_smt_interval                      50000
% 23.84/3.51  
% 23.84/3.51  ------ Superposition Simplification Setup
% 23.84/3.51  
% 23.84/3.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.84/3.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.84/3.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.84/3.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.84/3.51  --sup_full_triv                         [TrivRules;PropSubs]
% 23.84/3.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.84/3.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.84/3.51  --sup_immed_triv                        [TrivRules]
% 23.84/3.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.51  --sup_immed_bw_main                     []
% 23.84/3.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.84/3.51  --sup_input_triv                        [Unflattening;TrivRules]
% 23.84/3.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.84/3.51  --sup_input_bw                          []
% 23.84/3.51  
% 23.84/3.51  ------ Combination Options
% 23.84/3.51  
% 23.84/3.51  --comb_res_mult                         3
% 23.84/3.51  --comb_sup_mult                         2
% 23.84/3.51  --comb_inst_mult                        10
% 23.84/3.51  
% 23.84/3.51  ------ Debug Options
% 23.84/3.51  
% 23.84/3.51  --dbg_backtrace                         false
% 23.84/3.51  --dbg_dump_prop_clauses                 false
% 23.84/3.51  --dbg_dump_prop_clauses_file            -
% 23.84/3.51  --dbg_out_stat                          false
% 23.84/3.51  
% 23.84/3.51  
% 23.84/3.51  
% 23.84/3.51  
% 23.84/3.51  ------ Proving...
% 23.84/3.51  
% 23.84/3.51  
% 23.84/3.51  % SZS status Theorem for theBenchmark.p
% 23.84/3.51  
% 23.84/3.51   Resolution empty clause
% 23.84/3.51  
% 23.84/3.51  % SZS output start CNFRefutation for theBenchmark.p
% 23.84/3.51  
% 23.84/3.51  fof(f1,axiom,(
% 23.84/3.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f50,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.84/3.51    inference(cnf_transformation,[],[f1])).
% 23.84/3.51  
% 23.84/3.51  fof(f30,axiom,(
% 23.84/3.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f83,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 23.84/3.51    inference(cnf_transformation,[],[f30])).
% 23.84/3.51  
% 23.84/3.51  fof(f18,axiom,(
% 23.84/3.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f70,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.84/3.51    inference(cnf_transformation,[],[f18])).
% 23.84/3.51  
% 23.84/3.51  fof(f85,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.84/3.51    inference(definition_unfolding,[],[f83,f70])).
% 23.84/3.51  
% 23.84/3.51  fof(f87,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 23.84/3.51    inference(definition_unfolding,[],[f50,f85,f85])).
% 23.84/3.51  
% 23.84/3.51  fof(f28,axiom,(
% 23.84/3.51    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f81,plain,(
% 23.84/3.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 23.84/3.51    inference(cnf_transformation,[],[f28])).
% 23.84/3.51  
% 23.84/3.51  fof(f2,axiom,(
% 23.84/3.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f51,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 23.84/3.51    inference(cnf_transformation,[],[f2])).
% 23.84/3.51  
% 23.84/3.51  fof(f22,axiom,(
% 23.84/3.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f74,plain,(
% 23.84/3.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.84/3.51    inference(cnf_transformation,[],[f22])).
% 23.84/3.51  
% 23.84/3.51  fof(f29,axiom,(
% 23.84/3.51    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f82,plain,(
% 23.84/3.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 23.84/3.51    inference(cnf_transformation,[],[f29])).
% 23.84/3.51  
% 23.84/3.51  fof(f17,axiom,(
% 23.84/3.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f69,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.84/3.51    inference(cnf_transformation,[],[f17])).
% 23.84/3.51  
% 23.84/3.51  fof(f96,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.84/3.51    inference(definition_unfolding,[],[f69,f70])).
% 23.84/3.51  
% 23.84/3.51  fof(f8,axiom,(
% 23.84/3.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f59,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 23.84/3.51    inference(cnf_transformation,[],[f8])).
% 23.84/3.51  
% 23.84/3.51  fof(f86,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 23.84/3.51    inference(definition_unfolding,[],[f59,f85,f70])).
% 23.84/3.51  
% 23.84/3.51  fof(f23,axiom,(
% 23.84/3.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f75,plain,(
% 23.84/3.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 23.84/3.51    inference(cnf_transformation,[],[f23])).
% 23.84/3.51  
% 23.84/3.51  fof(f25,axiom,(
% 23.84/3.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f47,plain,(
% 23.84/3.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 23.84/3.51    inference(nnf_transformation,[],[f25])).
% 23.84/3.51  
% 23.84/3.51  fof(f77,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 23.84/3.51    inference(cnf_transformation,[],[f47])).
% 23.84/3.51  
% 23.84/3.51  fof(f24,axiom,(
% 23.84/3.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f76,plain,(
% 23.84/3.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 23.84/3.51    inference(cnf_transformation,[],[f24])).
% 23.84/3.51  
% 23.84/3.51  fof(f99,plain,(
% 23.84/3.51    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 23.84/3.51    inference(definition_unfolding,[],[f76,f85])).
% 23.84/3.51  
% 23.84/3.51  fof(f13,axiom,(
% 23.84/3.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f46,plain,(
% 23.84/3.51    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 23.84/3.51    inference(nnf_transformation,[],[f13])).
% 23.84/3.51  
% 23.84/3.51  fof(f65,plain,(
% 23.84/3.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 23.84/3.51    inference(cnf_transformation,[],[f46])).
% 23.84/3.51  
% 23.84/3.51  fof(f16,axiom,(
% 23.84/3.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f68,plain,(
% 23.84/3.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 23.84/3.51    inference(cnf_transformation,[],[f16])).
% 23.84/3.51  
% 23.84/3.51  fof(f95,plain,(
% 23.84/3.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 23.84/3.51    inference(definition_unfolding,[],[f68,f85])).
% 23.84/3.51  
% 23.84/3.51  fof(f12,axiom,(
% 23.84/3.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f63,plain,(
% 23.84/3.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.84/3.51    inference(cnf_transformation,[],[f12])).
% 23.84/3.51  
% 23.84/3.51  fof(f15,axiom,(
% 23.84/3.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f67,plain,(
% 23.84/3.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.84/3.51    inference(cnf_transformation,[],[f15])).
% 23.84/3.51  
% 23.84/3.51  fof(f64,plain,(
% 23.84/3.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 23.84/3.51    inference(cnf_transformation,[],[f46])).
% 23.84/3.51  
% 23.84/3.51  fof(f31,conjecture,(
% 23.84/3.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 23.84/3.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.84/3.51  
% 23.84/3.51  fof(f32,negated_conjecture,(
% 23.84/3.51    ~! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 23.84/3.51    inference(negated_conjecture,[],[f31])).
% 23.84/3.51  
% 23.84/3.51  fof(f39,plain,(
% 23.84/3.51    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 23.84/3.51    inference(ennf_transformation,[],[f32])).
% 23.84/3.51  
% 23.84/3.51  fof(f48,plain,(
% 23.84/3.51    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3))),
% 23.84/3.51    introduced(choice_axiom,[])).
% 23.84/3.51  
% 23.84/3.51  fof(f49,plain,(
% 23.84/3.51    ~r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3))),
% 23.84/3.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f48])).
% 23.84/3.51  
% 23.84/3.51  fof(f84,plain,(
% 23.84/3.51    ~r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3))),
% 23.84/3.51    inference(cnf_transformation,[],[f49])).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 23.84/3.51      inference(cnf_transformation,[],[f87]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_30,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 23.84/3.51      inference(cnf_transformation,[],[f81]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2,plain,
% 23.84/3.51      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 23.84/3.51      inference(cnf_transformation,[],[f51]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_425,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 23.84/3.51      inference(theory_normalisation,[status(thm)],[c_1,c_30,c_2]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_23,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.84/3.51      inference(cnf_transformation,[],[f74]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_920,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_30,c_2]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2335,plain,
% 23.84/3.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_23,c_920]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_31,plain,
% 23.84/3.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.84/3.51      inference(cnf_transformation,[],[f82]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1313,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_31,c_30]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1227,plain,
% 23.84/3.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_23,c_2]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1319,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_1313,c_1227]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1802,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2,c_1319]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2393,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2335,c_1802]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_919,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_30,c_2]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2600,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = k5_xboole_0(X2,k1_xboole_0) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2393,c_919]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2604,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = X2 ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_2600,c_23]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_6882,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X1 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_425,c_2604]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_19,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 23.84/3.51      inference(cnf_transformation,[],[f96]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_0,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 23.84/3.51      inference(cnf_transformation,[],[f86]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_426,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 23.84/3.51      inference(theory_normalisation,[status(thm)],[c_0,c_30,c_2]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_6721,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_19,c_426]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_6796,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_6721,c_23,c_31]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7069,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X1 ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_6882,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1876,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_1802,c_1802]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_921,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_30,c_2]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2750,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_921,c_1319]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2339,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_1802,c_920]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1870,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_30,c_1802]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_6593,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,k5_xboole_0(X3,X0)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2339,c_1870]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7070,plain,
% 23.84/3.51      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
% 23.84/3.51      inference(demodulation,
% 23.84/3.51                [status(thm)],
% 23.84/3.51                [c_7069,c_1876,c_2750,c_6593,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2752,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = X2 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_921,c_1802]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_11939,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X2),k5_xboole_0(X2,X0)) = k4_xboole_0(X1,X0) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_7070,c_2752]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2227,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_1876,c_30]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_4699,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_919,c_2227]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1872,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_1319,c_1802]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2141,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_1872,c_30]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_4360,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2141,c_2141]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_4838,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_4699,c_4360]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2219,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X0,X2) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_919,c_1876]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_6562,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X3)) = k5_xboole_0(X0,k5_xboole_0(X3,X1)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2339,c_2219]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_11966,plain,
% 23.84/3.51      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k4_xboole_0(X1,X0) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_11939,c_2339,c_4838,c_6562]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_24,plain,
% 23.84/3.51      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 23.84/3.51      inference(cnf_transformation,[],[f75]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_882,plain,
% 23.84/3.51      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 23.84/3.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_6746,plain,
% 23.84/3.51      ( r1_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_426,c_882]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7134,plain,
% 23.84/3.51      ( r1_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_6746,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_14691,plain,
% 23.84/3.51      ( r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0)))) = iProver_top ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_1319,c_7134]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_27,plain,
% 23.84/3.51      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 23.84/3.51      inference(cnf_transformation,[],[f77]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_879,plain,
% 23.84/3.51      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 23.84/3.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_42583,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0)))) = X0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_14691,c_879]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_25,plain,
% 23.84/3.51      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 23.84/3.51      inference(cnf_transformation,[],[f99]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_419,plain,
% 23.84/3.51      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 23.84/3.51      inference(theory_normalisation,[status(thm)],[c_25,c_30,c_2]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_881,plain,
% 23.84/3.51      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
% 23.84/3.51      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_12328,plain,
% 23.84/3.51      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_881,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_12329,plain,
% 23.84/3.51      ( r1_tarski(X0,k5_xboole_0(k4_xboole_0(X0,X1),X1)) = iProver_top ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_12328,c_2750]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_12333,plain,
% 23.84/3.51      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2,c_12329]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_14,plain,
% 23.84/3.51      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 23.84/3.51      inference(cnf_transformation,[],[f65]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_884,plain,
% 23.84/3.51      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 23.84/3.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_12390,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_12333,c_884]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_105680,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0))),X0)) = k1_xboole_0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_42583,c_12390]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_18,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 23.84/3.51      inference(cnf_transformation,[],[f95]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_420,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 23.84/3.51      inference(theory_normalisation,[status(thm)],[c_18,c_30,c_2]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1889,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k5_xboole_0(X1,X2),X3)))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_30,c_420]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2748,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X2,X0) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_921,c_1876]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_8821,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),X1) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_425,c_2748]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_9048,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),X1) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_8821,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_9049,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X1)) = k4_xboole_0(X0,X1) ),
% 23.84/3.51      inference(demodulation,
% 23.84/3.51                [status(thm)],
% 23.84/3.51                [c_9048,c_1319,c_1876,c_2748,c_4838,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_24741,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,X1),X0)))) = k4_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_920,c_9049]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2388,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2335,c_1876]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_13,plain,
% 23.84/3.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 23.84/3.51      inference(cnf_transformation,[],[f63]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_885,plain,
% 23.84/3.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 23.84/3.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_6745,plain,
% 23.84/3.51      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_426,c_885]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7135,plain,
% 23.84/3.51      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_6745,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7136,plain,
% 23.84/3.51      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1)) = iProver_top ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_7135,c_2750]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_15026,plain,
% 23.84/3.51      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0),k1_xboole_0)) = iProver_top ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2388,c_7136]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_15079,plain,
% 23.84/3.51      ( r1_tarski(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0)) = iProver_top ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_15026,c_23]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_17,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.84/3.51      inference(cnf_transformation,[],[f67]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_15080,plain,
% 23.84/3.51      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = iProver_top ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_15079,c_17]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_15404,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_15080,c_884]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_16219,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_15404,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_16262,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_16219,c_15404]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_16263,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_16262,c_2388]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1904,plain,
% 23.84/3.51      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = iProver_top ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_420,c_885]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_11275,plain,
% 23.84/3.51      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_1904,c_884]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_16716,plain,
% 23.84/3.51      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_16263,c_11275]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1806,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_30,c_1319]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_3133,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,X1) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2393,c_1806]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_3181,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_3133,c_23]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7325,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_425,c_3181]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7534,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1)))),X0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_7325,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_5630,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X2) = k5_xboole_0(X0,k5_xboole_0(X3,X1)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_921,c_2219]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7535,plain,
% 23.84/3.51      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k4_xboole_0(X1,X0) ),
% 23.84/3.51      inference(demodulation,
% 23.84/3.51                [status(thm)],
% 23.84/3.51                [c_7534,c_1876,c_2750,c_4838,c_5630,c_6796]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_18285,plain,
% 23.84/3.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_12390,c_7535]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_11936,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_7070,c_2604]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_18515,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_18285,c_11936]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_18516,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_18515,c_1227]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_59207,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k5_xboole_0(X1,X0),X2)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_16716,c_18516]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2351,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X0)) = X2 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_920,c_1872]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7921,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X1))))),k5_xboole_0(X1,X0)) = k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_425,c_2351]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2350,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X1,X0) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_920,c_1876]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2338,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_1876,c_920]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2361,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_2338,c_30]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_7767,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X1,X0)) = k5_xboole_0(X3,X2) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2350,c_2361]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_8139,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 23.84/3.51      inference(demodulation,
% 23.84/3.51                [status(thm)],
% 23.84/3.51                [c_7921,c_1319,c_2351,c_6796,c_7767]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_51097,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X0),X2),k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_16716,c_8139]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2555,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_30,c_2393]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2234,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X2,X1) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_1876,c_919]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_23178,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2555,c_2234]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_2500,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_30,c_2388]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_22379,plain,
% 23.84/3.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2,c_2500]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_23202,plain,
% 23.84/3.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_23178,c_2388,c_4838,c_22379]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_51208,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X0),X2))) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_51097,c_23,c_4838,c_23202]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_59553,plain,
% 23.84/3.51      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X1),X2))) ),
% 23.84/3.51      inference(light_normalisation,[status(thm)],[c_59207,c_2388,c_51208]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_83020,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_1889,c_24741,c_59553]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_83150,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X4,k5_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X3))),X4) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_2141,c_83020]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_83735,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X4,k5_xboole_0(X1,X3)))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X3,X1)),X4) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_83150,c_2339,c_23202]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_83736,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,X3)),X3))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X3,X1)),X2) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_83735,c_2361,c_4838]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_106011,plain,
% 23.84/3.51      ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_105680,c_4838,c_83736]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_15,plain,
% 23.84/3.51      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 23.84/3.51      inference(cnf_transformation,[],[f64]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_883,plain,
% 23.84/3.51      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 23.84/3.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_106618,plain,
% 23.84/3.51      ( r1_tarski(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = iProver_top ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_106011,c_883]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_108982,plain,
% 23.84/3.51      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k5_xboole_0(X0,X1)) = iProver_top ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_11966,c_106618]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1894,plain,
% 23.84/3.51      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_19,c_420]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_1935,plain,
% 23.84/3.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_1894,c_23,c_31]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_108992,plain,
% 23.84/3.51      ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 23.84/3.51      inference(demodulation,[status(thm)],[c_108982,c_1935]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_32,negated_conjecture,
% 23.84/3.51      ( ~ r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) ),
% 23.84/3.51      inference(cnf_transformation,[],[f84]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_876,plain,
% 23.84/3.51      ( r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) != iProver_top ),
% 23.84/3.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.84/3.51  
% 23.84/3.51  cnf(c_115254,plain,
% 23.84/3.51      ( $false ),
% 23.84/3.51      inference(superposition,[status(thm)],[c_108992,c_876]) ).
% 23.84/3.51  
% 23.84/3.51  
% 23.84/3.51  % SZS output end CNFRefutation for theBenchmark.p
% 23.84/3.51  
% 23.84/3.51  ------                               Statistics
% 23.84/3.51  
% 23.84/3.51  ------ General
% 23.84/3.51  
% 23.84/3.51  abstr_ref_over_cycles:                  0
% 23.84/3.51  abstr_ref_under_cycles:                 0
% 23.84/3.51  gc_basic_clause_elim:                   0
% 23.84/3.51  forced_gc_time:                         0
% 23.84/3.51  parsing_time:                           0.01
% 23.84/3.51  unif_index_cands_time:                  0.
% 23.84/3.51  unif_index_add_time:                    0.
% 23.84/3.51  orderings_time:                         0.
% 23.84/3.51  out_proof_time:                         0.011
% 23.84/3.51  total_time:                             2.948
% 23.84/3.51  num_of_symbols:                         42
% 23.84/3.51  num_of_terms:                           174972
% 23.84/3.51  
% 23.84/3.51  ------ Preprocessing
% 23.84/3.51  
% 23.84/3.51  num_of_splits:                          0
% 23.84/3.51  num_of_split_atoms:                     0
% 23.84/3.51  num_of_reused_defs:                     0
% 23.84/3.51  num_eq_ax_congr_red:                    6
% 23.84/3.51  num_of_sem_filtered_clauses:            1
% 23.84/3.51  num_of_subtypes:                        0
% 23.84/3.51  monotx_restored_types:                  0
% 23.84/3.51  sat_num_of_epr_types:                   0
% 23.84/3.51  sat_num_of_non_cyclic_types:            0
% 23.84/3.51  sat_guarded_non_collapsed_types:        0
% 23.84/3.51  num_pure_diseq_elim:                    0
% 23.84/3.51  simp_replaced_by:                       0
% 23.84/3.51  res_preprocessed:                       116
% 23.84/3.51  prep_upred:                             0
% 23.84/3.51  prep_unflattend:                        23
% 23.84/3.51  smt_new_axioms:                         0
% 23.84/3.51  pred_elim_cands:                        4
% 23.84/3.51  pred_elim:                              0
% 23.84/3.51  pred_elim_cl:                           0
% 23.84/3.51  pred_elim_cycles:                       2
% 23.84/3.51  merged_defs:                            12
% 23.84/3.51  merged_defs_ncl:                        0
% 23.84/3.51  bin_hyper_res:                          12
% 23.84/3.51  prep_cycles:                            3
% 23.84/3.51  pred_elim_time:                         0.003
% 23.84/3.51  splitting_time:                         0.
% 23.84/3.51  sem_filter_time:                        0.
% 23.84/3.51  monotx_time:                            0.
% 23.84/3.51  subtype_inf_time:                       0.
% 23.84/3.51  
% 23.84/3.51  ------ Problem properties
% 23.84/3.51  
% 23.84/3.51  clauses:                                33
% 23.84/3.51  conjectures:                            1
% 23.84/3.51  epr:                                    4
% 23.84/3.51  horn:                                   31
% 23.84/3.51  ground:                                 2
% 23.84/3.51  unary:                                  22
% 23.84/3.51  binary:                                 10
% 23.84/3.51  lits:                                   45
% 23.84/3.51  lits_eq:                                21
% 23.84/3.51  fd_pure:                                0
% 23.84/3.51  fd_pseudo:                              0
% 23.84/3.51  fd_cond:                                0
% 23.84/3.51  fd_pseudo_cond:                         1
% 23.84/3.51  ac_symbols:                             1
% 23.84/3.51  
% 23.84/3.51  ------ Propositional Solver
% 23.84/3.51  
% 23.84/3.51  prop_solver_calls:                      31
% 23.84/3.51  prop_fast_solver_calls:                 805
% 23.84/3.51  smt_solver_calls:                       0
% 23.84/3.51  smt_fast_solver_calls:                  0
% 23.84/3.51  prop_num_of_clauses:                    28388
% 23.84/3.51  prop_preprocess_simplified:             28338
% 23.84/3.51  prop_fo_subsumed:                       1
% 23.84/3.51  prop_solver_time:                       0.
% 23.84/3.51  smt_solver_time:                        0.
% 23.84/3.51  smt_fast_solver_time:                   0.
% 23.84/3.51  prop_fast_solver_time:                  0.
% 23.84/3.51  prop_unsat_core_time:                   0.
% 23.84/3.51  
% 23.84/3.51  ------ QBF
% 23.84/3.51  
% 23.84/3.51  qbf_q_res:                              0
% 23.84/3.51  qbf_num_tautologies:                    0
% 23.84/3.51  qbf_prep_cycles:                        0
% 23.84/3.51  
% 23.84/3.51  ------ BMC1
% 23.84/3.51  
% 23.84/3.51  bmc1_current_bound:                     -1
% 23.84/3.51  bmc1_last_solved_bound:                 -1
% 23.84/3.51  bmc1_unsat_core_size:                   -1
% 23.84/3.51  bmc1_unsat_core_parents_size:           -1
% 23.84/3.51  bmc1_merge_next_fun:                    0
% 23.84/3.51  bmc1_unsat_core_clauses_time:           0.
% 23.84/3.51  
% 23.84/3.51  ------ Instantiation
% 23.84/3.51  
% 23.84/3.51  inst_num_of_clauses:                    4208
% 23.84/3.51  inst_num_in_passive:                    2756
% 23.84/3.51  inst_num_in_active:                     1206
% 23.84/3.51  inst_num_in_unprocessed:                248
% 23.84/3.51  inst_num_of_loops:                      1640
% 23.84/3.51  inst_num_of_learning_restarts:          0
% 23.84/3.51  inst_num_moves_active_passive:          430
% 23.84/3.51  inst_lit_activity:                      0
% 23.84/3.51  inst_lit_activity_moves:                0
% 23.84/3.51  inst_num_tautologies:                   0
% 23.84/3.51  inst_num_prop_implied:                  0
% 23.84/3.51  inst_num_existing_simplified:           0
% 23.84/3.51  inst_num_eq_res_simplified:             0
% 23.84/3.51  inst_num_child_elim:                    0
% 23.84/3.51  inst_num_of_dismatching_blockings:      2987
% 23.84/3.51  inst_num_of_non_proper_insts:           5100
% 23.84/3.51  inst_num_of_duplicates:                 0
% 23.84/3.51  inst_inst_num_from_inst_to_res:         0
% 23.84/3.51  inst_dismatching_checking_time:         0.
% 23.84/3.51  
% 23.84/3.51  ------ Resolution
% 23.84/3.51  
% 23.84/3.51  res_num_of_clauses:                     0
% 23.84/3.51  res_num_in_passive:                     0
% 23.84/3.51  res_num_in_active:                      0
% 23.84/3.51  res_num_of_loops:                       119
% 23.84/3.51  res_forward_subset_subsumed:            805
% 23.84/3.51  res_backward_subset_subsumed:           8
% 23.84/3.51  res_forward_subsumed:                   0
% 23.84/3.51  res_backward_subsumed:                  0
% 23.84/3.51  res_forward_subsumption_resolution:     0
% 23.84/3.51  res_backward_subsumption_resolution:    0
% 23.84/3.51  res_clause_to_clause_subsumption:       227978
% 23.84/3.51  res_orphan_elimination:                 0
% 23.84/3.51  res_tautology_del:                      245
% 23.84/3.51  res_num_eq_res_simplified:              0
% 23.84/3.51  res_num_sel_changes:                    0
% 23.84/3.51  res_moves_from_active_to_pass:          0
% 23.84/3.51  
% 23.84/3.51  ------ Superposition
% 23.84/3.51  
% 23.84/3.51  sup_time_total:                         0.
% 23.84/3.51  sup_time_generating:                    0.
% 23.84/3.51  sup_time_sim_full:                      0.
% 23.84/3.51  sup_time_sim_immed:                     0.
% 23.84/3.51  
% 23.84/3.51  sup_num_of_clauses:                     8474
% 23.84/3.51  sup_num_in_active:                      297
% 23.84/3.51  sup_num_in_passive:                     8177
% 23.84/3.51  sup_num_of_loops:                       326
% 23.84/3.51  sup_fw_superposition:                   29080
% 23.84/3.51  sup_bw_superposition:                   23278
% 23.84/3.51  sup_immediate_simplified:               24527
% 23.84/3.51  sup_given_eliminated:                   12
% 23.84/3.51  comparisons_done:                       0
% 23.84/3.51  comparisons_avoided:                    0
% 23.84/3.51  
% 23.84/3.51  ------ Simplifications
% 23.84/3.51  
% 23.84/3.51  
% 23.84/3.51  sim_fw_subset_subsumed:                 27
% 23.84/3.51  sim_bw_subset_subsumed:                 0
% 23.84/3.51  sim_fw_subsumed:                        3672
% 23.84/3.51  sim_bw_subsumed:                        51
% 23.84/3.51  sim_fw_subsumption_res:                 0
% 23.84/3.51  sim_bw_subsumption_res:                 0
% 23.84/3.51  sim_tautology_del:                      2
% 23.84/3.51  sim_eq_tautology_del:                   4463
% 23.84/3.51  sim_eq_res_simp:                        0
% 23.84/3.51  sim_fw_demodulated:                     19163
% 23.84/3.51  sim_bw_demodulated:                     292
% 23.84/3.51  sim_light_normalised:                   8717
% 23.84/3.51  sim_joinable_taut:                      344
% 23.84/3.51  sim_joinable_simp:                      1
% 23.84/3.51  sim_ac_normalised:                      0
% 23.84/3.51  sim_smt_subsumption:                    0
% 23.84/3.51  
%------------------------------------------------------------------------------
