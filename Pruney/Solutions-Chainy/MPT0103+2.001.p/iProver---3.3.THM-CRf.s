%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:08 EST 2020

% Result     : Theorem 27.71s
% Output     : CNFRefutation 27.71s
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

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f61,f85,f70])).

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

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f60,plain,(
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

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
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

cnf(c_42585,plain,
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

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_886,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12390,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12333,c_886])).

cnf(c_105682,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0))),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_42585,c_12390])).

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

cnf(c_15,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_883,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6745,plain,
    ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_426,c_883])).

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
    inference(superposition,[status(thm)],[c_15080,c_886])).

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
    inference(superposition,[status(thm)],[c_420,c_883])).

cnf(c_11275,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1904,c_886])).

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

cnf(c_59209,plain,
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

cnf(c_51099,plain,
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

cnf(c_51210,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X0),X2))) ),
    inference(demodulation,[status(thm)],[c_51099,c_23,c_4838,c_23202])).

cnf(c_59555,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X1),X2))) ),
    inference(light_normalisation,[status(thm)],[c_59209,c_2388,c_51210])).

cnf(c_83022,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_1889,c_24741,c_59555])).

cnf(c_83152,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X4,k5_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X3))),X4) ),
    inference(superposition,[status(thm)],[c_2141,c_83022])).

cnf(c_83737,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X4,k5_xboole_0(X1,X3)))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X3,X1)),X4) ),
    inference(demodulation,[status(thm)],[c_83152,c_2339,c_23202])).

cnf(c_83738,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,X3)),X3))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X3,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_83737,c_2361,c_4838])).

cnf(c_106013,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_105682,c_4838,c_83738])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_885,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_106620,plain,
    ( r1_tarski(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_106013,c_885])).

cnf(c_108984,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11966,c_106620])).

cnf(c_1894,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_19,c_420])).

cnf(c_1935,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1894,c_23,c_31])).

cnf(c_108994,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_108984,c_1935])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_876,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_115256,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_108994,c_876])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:26:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.71/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.71/3.98  
% 27.71/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.71/3.98  
% 27.71/3.98  ------  iProver source info
% 27.71/3.98  
% 27.71/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.71/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.71/3.98  git: non_committed_changes: false
% 27.71/3.98  git: last_make_outside_of_git: false
% 27.71/3.98  
% 27.71/3.98  ------ 
% 27.71/3.98  
% 27.71/3.98  ------ Input Options
% 27.71/3.98  
% 27.71/3.98  --out_options                           all
% 27.71/3.98  --tptp_safe_out                         true
% 27.71/3.98  --problem_path                          ""
% 27.71/3.98  --include_path                          ""
% 27.71/3.98  --clausifier                            res/vclausify_rel
% 27.71/3.98  --clausifier_options                    ""
% 27.71/3.98  --stdin                                 false
% 27.71/3.98  --stats_out                             all
% 27.71/3.98  
% 27.71/3.98  ------ General Options
% 27.71/3.98  
% 27.71/3.98  --fof                                   false
% 27.71/3.98  --time_out_real                         305.
% 27.71/3.98  --time_out_virtual                      -1.
% 27.71/3.98  --symbol_type_check                     false
% 27.71/3.98  --clausify_out                          false
% 27.71/3.98  --sig_cnt_out                           false
% 27.71/3.98  --trig_cnt_out                          false
% 27.71/3.98  --trig_cnt_out_tolerance                1.
% 27.71/3.98  --trig_cnt_out_sk_spl                   false
% 27.71/3.98  --abstr_cl_out                          false
% 27.71/3.98  
% 27.71/3.98  ------ Global Options
% 27.71/3.98  
% 27.71/3.98  --schedule                              default
% 27.71/3.98  --add_important_lit                     false
% 27.71/3.98  --prop_solver_per_cl                    1000
% 27.71/3.98  --min_unsat_core                        false
% 27.71/3.98  --soft_assumptions                      false
% 27.71/3.98  --soft_lemma_size                       3
% 27.71/3.98  --prop_impl_unit_size                   0
% 27.71/3.98  --prop_impl_unit                        []
% 27.71/3.98  --share_sel_clauses                     true
% 27.71/3.98  --reset_solvers                         false
% 27.71/3.98  --bc_imp_inh                            [conj_cone]
% 27.71/3.98  --conj_cone_tolerance                   3.
% 27.71/3.98  --extra_neg_conj                        none
% 27.71/3.98  --large_theory_mode                     true
% 27.71/3.98  --prolific_symb_bound                   200
% 27.71/3.98  --lt_threshold                          2000
% 27.71/3.98  --clause_weak_htbl                      true
% 27.71/3.98  --gc_record_bc_elim                     false
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing Options
% 27.71/3.98  
% 27.71/3.98  --preprocessing_flag                    true
% 27.71/3.98  --time_out_prep_mult                    0.1
% 27.71/3.98  --splitting_mode                        input
% 27.71/3.98  --splitting_grd                         true
% 27.71/3.98  --splitting_cvd                         false
% 27.71/3.98  --splitting_cvd_svl                     false
% 27.71/3.98  --splitting_nvd                         32
% 27.71/3.98  --sub_typing                            true
% 27.71/3.98  --prep_gs_sim                           true
% 27.71/3.98  --prep_unflatten                        true
% 27.71/3.98  --prep_res_sim                          true
% 27.71/3.98  --prep_upred                            true
% 27.71/3.98  --prep_sem_filter                       exhaustive
% 27.71/3.98  --prep_sem_filter_out                   false
% 27.71/3.98  --pred_elim                             true
% 27.71/3.98  --res_sim_input                         true
% 27.71/3.98  --eq_ax_congr_red                       true
% 27.71/3.98  --pure_diseq_elim                       true
% 27.71/3.98  --brand_transform                       false
% 27.71/3.98  --non_eq_to_eq                          false
% 27.71/3.98  --prep_def_merge                        true
% 27.71/3.98  --prep_def_merge_prop_impl              false
% 27.71/3.98  --prep_def_merge_mbd                    true
% 27.71/3.98  --prep_def_merge_tr_red                 false
% 27.71/3.98  --prep_def_merge_tr_cl                  false
% 27.71/3.98  --smt_preprocessing                     true
% 27.71/3.98  --smt_ac_axioms                         fast
% 27.71/3.98  --preprocessed_out                      false
% 27.71/3.98  --preprocessed_stats                    false
% 27.71/3.98  
% 27.71/3.98  ------ Abstraction refinement Options
% 27.71/3.98  
% 27.71/3.98  --abstr_ref                             []
% 27.71/3.98  --abstr_ref_prep                        false
% 27.71/3.98  --abstr_ref_until_sat                   false
% 27.71/3.98  --abstr_ref_sig_restrict                funpre
% 27.71/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.71/3.98  --abstr_ref_under                       []
% 27.71/3.98  
% 27.71/3.98  ------ SAT Options
% 27.71/3.98  
% 27.71/3.98  --sat_mode                              false
% 27.71/3.98  --sat_fm_restart_options                ""
% 27.71/3.98  --sat_gr_def                            false
% 27.71/3.98  --sat_epr_types                         true
% 27.71/3.98  --sat_non_cyclic_types                  false
% 27.71/3.98  --sat_finite_models                     false
% 27.71/3.98  --sat_fm_lemmas                         false
% 27.71/3.98  --sat_fm_prep                           false
% 27.71/3.98  --sat_fm_uc_incr                        true
% 27.71/3.98  --sat_out_model                         small
% 27.71/3.98  --sat_out_clauses                       false
% 27.71/3.98  
% 27.71/3.98  ------ QBF Options
% 27.71/3.98  
% 27.71/3.98  --qbf_mode                              false
% 27.71/3.98  --qbf_elim_univ                         false
% 27.71/3.98  --qbf_dom_inst                          none
% 27.71/3.98  --qbf_dom_pre_inst                      false
% 27.71/3.98  --qbf_sk_in                             false
% 27.71/3.98  --qbf_pred_elim                         true
% 27.71/3.98  --qbf_split                             512
% 27.71/3.98  
% 27.71/3.98  ------ BMC1 Options
% 27.71/3.98  
% 27.71/3.98  --bmc1_incremental                      false
% 27.71/3.98  --bmc1_axioms                           reachable_all
% 27.71/3.98  --bmc1_min_bound                        0
% 27.71/3.98  --bmc1_max_bound                        -1
% 27.71/3.98  --bmc1_max_bound_default                -1
% 27.71/3.98  --bmc1_symbol_reachability              true
% 27.71/3.98  --bmc1_property_lemmas                  false
% 27.71/3.98  --bmc1_k_induction                      false
% 27.71/3.98  --bmc1_non_equiv_states                 false
% 27.71/3.98  --bmc1_deadlock                         false
% 27.71/3.98  --bmc1_ucm                              false
% 27.71/3.98  --bmc1_add_unsat_core                   none
% 27.71/3.98  --bmc1_unsat_core_children              false
% 27.71/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.71/3.98  --bmc1_out_stat                         full
% 27.71/3.98  --bmc1_ground_init                      false
% 27.71/3.98  --bmc1_pre_inst_next_state              false
% 27.71/3.98  --bmc1_pre_inst_state                   false
% 27.71/3.98  --bmc1_pre_inst_reach_state             false
% 27.71/3.98  --bmc1_out_unsat_core                   false
% 27.71/3.98  --bmc1_aig_witness_out                  false
% 27.71/3.98  --bmc1_verbose                          false
% 27.71/3.98  --bmc1_dump_clauses_tptp                false
% 27.71/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.71/3.98  --bmc1_dump_file                        -
% 27.71/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.71/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.71/3.98  --bmc1_ucm_extend_mode                  1
% 27.71/3.98  --bmc1_ucm_init_mode                    2
% 27.71/3.98  --bmc1_ucm_cone_mode                    none
% 27.71/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.71/3.98  --bmc1_ucm_relax_model                  4
% 27.71/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.71/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.71/3.98  --bmc1_ucm_layered_model                none
% 27.71/3.98  --bmc1_ucm_max_lemma_size               10
% 27.71/3.98  
% 27.71/3.98  ------ AIG Options
% 27.71/3.98  
% 27.71/3.98  --aig_mode                              false
% 27.71/3.98  
% 27.71/3.98  ------ Instantiation Options
% 27.71/3.98  
% 27.71/3.98  --instantiation_flag                    true
% 27.71/3.98  --inst_sos_flag                         true
% 27.71/3.98  --inst_sos_phase                        true
% 27.71/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.71/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.71/3.98  --inst_lit_sel_side                     num_symb
% 27.71/3.98  --inst_solver_per_active                1400
% 27.71/3.98  --inst_solver_calls_frac                1.
% 27.71/3.98  --inst_passive_queue_type               priority_queues
% 27.71/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.71/3.98  --inst_passive_queues_freq              [25;2]
% 27.71/3.98  --inst_dismatching                      true
% 27.71/3.98  --inst_eager_unprocessed_to_passive     true
% 27.71/3.98  --inst_prop_sim_given                   true
% 27.71/3.98  --inst_prop_sim_new                     false
% 27.71/3.98  --inst_subs_new                         false
% 27.71/3.98  --inst_eq_res_simp                      false
% 27.71/3.98  --inst_subs_given                       false
% 27.71/3.98  --inst_orphan_elimination               true
% 27.71/3.98  --inst_learning_loop_flag               true
% 27.71/3.98  --inst_learning_start                   3000
% 27.71/3.98  --inst_learning_factor                  2
% 27.71/3.98  --inst_start_prop_sim_after_learn       3
% 27.71/3.98  --inst_sel_renew                        solver
% 27.71/3.98  --inst_lit_activity_flag                true
% 27.71/3.98  --inst_restr_to_given                   false
% 27.71/3.98  --inst_activity_threshold               500
% 27.71/3.98  --inst_out_proof                        true
% 27.71/3.98  
% 27.71/3.98  ------ Resolution Options
% 27.71/3.98  
% 27.71/3.98  --resolution_flag                       true
% 27.71/3.98  --res_lit_sel                           adaptive
% 27.71/3.98  --res_lit_sel_side                      none
% 27.71/3.98  --res_ordering                          kbo
% 27.71/3.98  --res_to_prop_solver                    active
% 27.71/3.98  --res_prop_simpl_new                    false
% 27.71/3.98  --res_prop_simpl_given                  true
% 27.71/3.98  --res_passive_queue_type                priority_queues
% 27.71/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.71/3.98  --res_passive_queues_freq               [15;5]
% 27.71/3.98  --res_forward_subs                      full
% 27.71/3.98  --res_backward_subs                     full
% 27.71/3.98  --res_forward_subs_resolution           true
% 27.71/3.98  --res_backward_subs_resolution          true
% 27.71/3.98  --res_orphan_elimination                true
% 27.71/3.98  --res_time_limit                        2.
% 27.71/3.98  --res_out_proof                         true
% 27.71/3.98  
% 27.71/3.98  ------ Superposition Options
% 27.71/3.98  
% 27.71/3.98  --superposition_flag                    true
% 27.71/3.98  --sup_passive_queue_type                priority_queues
% 27.71/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.71/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.71/3.98  --demod_completeness_check              fast
% 27.71/3.98  --demod_use_ground                      true
% 27.71/3.98  --sup_to_prop_solver                    passive
% 27.71/3.98  --sup_prop_simpl_new                    true
% 27.71/3.98  --sup_prop_simpl_given                  true
% 27.71/3.98  --sup_fun_splitting                     true
% 27.71/3.98  --sup_smt_interval                      50000
% 27.71/3.98  
% 27.71/3.98  ------ Superposition Simplification Setup
% 27.71/3.98  
% 27.71/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.71/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.71/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.71/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.71/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.71/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.71/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.71/3.98  --sup_immed_triv                        [TrivRules]
% 27.71/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_immed_bw_main                     []
% 27.71/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.71/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.71/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_input_bw                          []
% 27.71/3.98  
% 27.71/3.98  ------ Combination Options
% 27.71/3.98  
% 27.71/3.98  --comb_res_mult                         3
% 27.71/3.98  --comb_sup_mult                         2
% 27.71/3.98  --comb_inst_mult                        10
% 27.71/3.98  
% 27.71/3.98  ------ Debug Options
% 27.71/3.98  
% 27.71/3.98  --dbg_backtrace                         false
% 27.71/3.98  --dbg_dump_prop_clauses                 false
% 27.71/3.98  --dbg_dump_prop_clauses_file            -
% 27.71/3.98  --dbg_out_stat                          false
% 27.71/3.98  ------ Parsing...
% 27.71/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.71/3.98  ------ Proving...
% 27.71/3.98  ------ Problem Properties 
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  clauses                                 33
% 27.71/3.98  conjectures                             1
% 27.71/3.98  EPR                                     4
% 27.71/3.98  Horn                                    31
% 27.71/3.98  unary                                   22
% 27.71/3.98  binary                                  10
% 27.71/3.98  lits                                    45
% 27.71/3.98  lits eq                                 21
% 27.71/3.98  fd_pure                                 0
% 27.71/3.98  fd_pseudo                               0
% 27.71/3.98  fd_cond                                 0
% 27.71/3.98  fd_pseudo_cond                          1
% 27.71/3.98  AC symbols                              1
% 27.71/3.98  
% 27.71/3.98  ------ Schedule dynamic 5 is on 
% 27.71/3.98  
% 27.71/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  ------ 
% 27.71/3.98  Current options:
% 27.71/3.98  ------ 
% 27.71/3.98  
% 27.71/3.98  ------ Input Options
% 27.71/3.98  
% 27.71/3.98  --out_options                           all
% 27.71/3.98  --tptp_safe_out                         true
% 27.71/3.98  --problem_path                          ""
% 27.71/3.98  --include_path                          ""
% 27.71/3.98  --clausifier                            res/vclausify_rel
% 27.71/3.98  --clausifier_options                    ""
% 27.71/3.98  --stdin                                 false
% 27.71/3.98  --stats_out                             all
% 27.71/3.98  
% 27.71/3.98  ------ General Options
% 27.71/3.98  
% 27.71/3.98  --fof                                   false
% 27.71/3.98  --time_out_real                         305.
% 27.71/3.98  --time_out_virtual                      -1.
% 27.71/3.98  --symbol_type_check                     false
% 27.71/3.98  --clausify_out                          false
% 27.71/3.98  --sig_cnt_out                           false
% 27.71/3.98  --trig_cnt_out                          false
% 27.71/3.98  --trig_cnt_out_tolerance                1.
% 27.71/3.98  --trig_cnt_out_sk_spl                   false
% 27.71/3.98  --abstr_cl_out                          false
% 27.71/3.98  
% 27.71/3.98  ------ Global Options
% 27.71/3.98  
% 27.71/3.98  --schedule                              default
% 27.71/3.98  --add_important_lit                     false
% 27.71/3.98  --prop_solver_per_cl                    1000
% 27.71/3.98  --min_unsat_core                        false
% 27.71/3.98  --soft_assumptions                      false
% 27.71/3.98  --soft_lemma_size                       3
% 27.71/3.98  --prop_impl_unit_size                   0
% 27.71/3.98  --prop_impl_unit                        []
% 27.71/3.98  --share_sel_clauses                     true
% 27.71/3.98  --reset_solvers                         false
% 27.71/3.98  --bc_imp_inh                            [conj_cone]
% 27.71/3.98  --conj_cone_tolerance                   3.
% 27.71/3.98  --extra_neg_conj                        none
% 27.71/3.98  --large_theory_mode                     true
% 27.71/3.98  --prolific_symb_bound                   200
% 27.71/3.98  --lt_threshold                          2000
% 27.71/3.98  --clause_weak_htbl                      true
% 27.71/3.98  --gc_record_bc_elim                     false
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing Options
% 27.71/3.98  
% 27.71/3.98  --preprocessing_flag                    true
% 27.71/3.98  --time_out_prep_mult                    0.1
% 27.71/3.98  --splitting_mode                        input
% 27.71/3.98  --splitting_grd                         true
% 27.71/3.98  --splitting_cvd                         false
% 27.71/3.98  --splitting_cvd_svl                     false
% 27.71/3.98  --splitting_nvd                         32
% 27.71/3.98  --sub_typing                            true
% 27.71/3.98  --prep_gs_sim                           true
% 27.71/3.98  --prep_unflatten                        true
% 27.71/3.98  --prep_res_sim                          true
% 27.71/3.98  --prep_upred                            true
% 27.71/3.98  --prep_sem_filter                       exhaustive
% 27.71/3.98  --prep_sem_filter_out                   false
% 27.71/3.98  --pred_elim                             true
% 27.71/3.98  --res_sim_input                         true
% 27.71/3.98  --eq_ax_congr_red                       true
% 27.71/3.98  --pure_diseq_elim                       true
% 27.71/3.98  --brand_transform                       false
% 27.71/3.98  --non_eq_to_eq                          false
% 27.71/3.98  --prep_def_merge                        true
% 27.71/3.98  --prep_def_merge_prop_impl              false
% 27.71/3.98  --prep_def_merge_mbd                    true
% 27.71/3.98  --prep_def_merge_tr_red                 false
% 27.71/3.98  --prep_def_merge_tr_cl                  false
% 27.71/3.98  --smt_preprocessing                     true
% 27.71/3.98  --smt_ac_axioms                         fast
% 27.71/3.98  --preprocessed_out                      false
% 27.71/3.98  --preprocessed_stats                    false
% 27.71/3.98  
% 27.71/3.98  ------ Abstraction refinement Options
% 27.71/3.98  
% 27.71/3.98  --abstr_ref                             []
% 27.71/3.98  --abstr_ref_prep                        false
% 27.71/3.98  --abstr_ref_until_sat                   false
% 27.71/3.98  --abstr_ref_sig_restrict                funpre
% 27.71/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.71/3.98  --abstr_ref_under                       []
% 27.71/3.98  
% 27.71/3.98  ------ SAT Options
% 27.71/3.98  
% 27.71/3.98  --sat_mode                              false
% 27.71/3.98  --sat_fm_restart_options                ""
% 27.71/3.98  --sat_gr_def                            false
% 27.71/3.98  --sat_epr_types                         true
% 27.71/3.98  --sat_non_cyclic_types                  false
% 27.71/3.98  --sat_finite_models                     false
% 27.71/3.98  --sat_fm_lemmas                         false
% 27.71/3.98  --sat_fm_prep                           false
% 27.71/3.98  --sat_fm_uc_incr                        true
% 27.71/3.98  --sat_out_model                         small
% 27.71/3.98  --sat_out_clauses                       false
% 27.71/3.98  
% 27.71/3.98  ------ QBF Options
% 27.71/3.98  
% 27.71/3.98  --qbf_mode                              false
% 27.71/3.98  --qbf_elim_univ                         false
% 27.71/3.98  --qbf_dom_inst                          none
% 27.71/3.98  --qbf_dom_pre_inst                      false
% 27.71/3.98  --qbf_sk_in                             false
% 27.71/3.98  --qbf_pred_elim                         true
% 27.71/3.98  --qbf_split                             512
% 27.71/3.98  
% 27.71/3.98  ------ BMC1 Options
% 27.71/3.98  
% 27.71/3.98  --bmc1_incremental                      false
% 27.71/3.98  --bmc1_axioms                           reachable_all
% 27.71/3.98  --bmc1_min_bound                        0
% 27.71/3.98  --bmc1_max_bound                        -1
% 27.71/3.98  --bmc1_max_bound_default                -1
% 27.71/3.98  --bmc1_symbol_reachability              true
% 27.71/3.98  --bmc1_property_lemmas                  false
% 27.71/3.98  --bmc1_k_induction                      false
% 27.71/3.98  --bmc1_non_equiv_states                 false
% 27.71/3.98  --bmc1_deadlock                         false
% 27.71/3.98  --bmc1_ucm                              false
% 27.71/3.98  --bmc1_add_unsat_core                   none
% 27.71/3.98  --bmc1_unsat_core_children              false
% 27.71/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.71/3.98  --bmc1_out_stat                         full
% 27.71/3.98  --bmc1_ground_init                      false
% 27.71/3.98  --bmc1_pre_inst_next_state              false
% 27.71/3.98  --bmc1_pre_inst_state                   false
% 27.71/3.98  --bmc1_pre_inst_reach_state             false
% 27.71/3.98  --bmc1_out_unsat_core                   false
% 27.71/3.98  --bmc1_aig_witness_out                  false
% 27.71/3.98  --bmc1_verbose                          false
% 27.71/3.98  --bmc1_dump_clauses_tptp                false
% 27.71/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.71/3.98  --bmc1_dump_file                        -
% 27.71/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.71/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.71/3.98  --bmc1_ucm_extend_mode                  1
% 27.71/3.98  --bmc1_ucm_init_mode                    2
% 27.71/3.98  --bmc1_ucm_cone_mode                    none
% 27.71/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.71/3.98  --bmc1_ucm_relax_model                  4
% 27.71/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.71/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.71/3.98  --bmc1_ucm_layered_model                none
% 27.71/3.98  --bmc1_ucm_max_lemma_size               10
% 27.71/3.98  
% 27.71/3.98  ------ AIG Options
% 27.71/3.98  
% 27.71/3.98  --aig_mode                              false
% 27.71/3.98  
% 27.71/3.98  ------ Instantiation Options
% 27.71/3.98  
% 27.71/3.98  --instantiation_flag                    true
% 27.71/3.98  --inst_sos_flag                         true
% 27.71/3.98  --inst_sos_phase                        true
% 27.71/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.71/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.71/3.98  --inst_lit_sel_side                     none
% 27.71/3.98  --inst_solver_per_active                1400
% 27.71/3.98  --inst_solver_calls_frac                1.
% 27.71/3.98  --inst_passive_queue_type               priority_queues
% 27.71/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.71/3.98  --inst_passive_queues_freq              [25;2]
% 27.71/3.98  --inst_dismatching                      true
% 27.71/3.98  --inst_eager_unprocessed_to_passive     true
% 27.71/3.98  --inst_prop_sim_given                   true
% 27.71/3.98  --inst_prop_sim_new                     false
% 27.71/3.98  --inst_subs_new                         false
% 27.71/3.98  --inst_eq_res_simp                      false
% 27.71/3.98  --inst_subs_given                       false
% 27.71/3.98  --inst_orphan_elimination               true
% 27.71/3.98  --inst_learning_loop_flag               true
% 27.71/3.98  --inst_learning_start                   3000
% 27.71/3.98  --inst_learning_factor                  2
% 27.71/3.98  --inst_start_prop_sim_after_learn       3
% 27.71/3.98  --inst_sel_renew                        solver
% 27.71/3.98  --inst_lit_activity_flag                true
% 27.71/3.98  --inst_restr_to_given                   false
% 27.71/3.98  --inst_activity_threshold               500
% 27.71/3.98  --inst_out_proof                        true
% 27.71/3.98  
% 27.71/3.98  ------ Resolution Options
% 27.71/3.98  
% 27.71/3.98  --resolution_flag                       false
% 27.71/3.98  --res_lit_sel                           adaptive
% 27.71/3.98  --res_lit_sel_side                      none
% 27.71/3.98  --res_ordering                          kbo
% 27.71/3.98  --res_to_prop_solver                    active
% 27.71/3.98  --res_prop_simpl_new                    false
% 27.71/3.98  --res_prop_simpl_given                  true
% 27.71/3.98  --res_passive_queue_type                priority_queues
% 27.71/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.71/3.98  --res_passive_queues_freq               [15;5]
% 27.71/3.98  --res_forward_subs                      full
% 27.71/3.98  --res_backward_subs                     full
% 27.71/3.98  --res_forward_subs_resolution           true
% 27.71/3.98  --res_backward_subs_resolution          true
% 27.71/3.98  --res_orphan_elimination                true
% 27.71/3.98  --res_time_limit                        2.
% 27.71/3.98  --res_out_proof                         true
% 27.71/3.98  
% 27.71/3.98  ------ Superposition Options
% 27.71/3.98  
% 27.71/3.98  --superposition_flag                    true
% 27.71/3.98  --sup_passive_queue_type                priority_queues
% 27.71/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.71/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.71/3.98  --demod_completeness_check              fast
% 27.71/3.98  --demod_use_ground                      true
% 27.71/3.98  --sup_to_prop_solver                    passive
% 27.71/3.98  --sup_prop_simpl_new                    true
% 27.71/3.98  --sup_prop_simpl_given                  true
% 27.71/3.98  --sup_fun_splitting                     true
% 27.71/3.98  --sup_smt_interval                      50000
% 27.71/3.98  
% 27.71/3.98  ------ Superposition Simplification Setup
% 27.71/3.98  
% 27.71/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.71/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.71/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.71/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.71/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.71/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.71/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.71/3.98  --sup_immed_triv                        [TrivRules]
% 27.71/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_immed_bw_main                     []
% 27.71/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.71/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.71/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.71/3.98  --sup_input_bw                          []
% 27.71/3.98  
% 27.71/3.98  ------ Combination Options
% 27.71/3.98  
% 27.71/3.98  --comb_res_mult                         3
% 27.71/3.98  --comb_sup_mult                         2
% 27.71/3.98  --comb_inst_mult                        10
% 27.71/3.98  
% 27.71/3.98  ------ Debug Options
% 27.71/3.98  
% 27.71/3.98  --dbg_backtrace                         false
% 27.71/3.98  --dbg_dump_prop_clauses                 false
% 27.71/3.98  --dbg_dump_prop_clauses_file            -
% 27.71/3.98  --dbg_out_stat                          false
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  ------ Proving...
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  % SZS status Theorem for theBenchmark.p
% 27.71/3.98  
% 27.71/3.98   Resolution empty clause
% 27.71/3.98  
% 27.71/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.71/3.98  
% 27.71/3.98  fof(f1,axiom,(
% 27.71/3.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f50,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f1])).
% 27.71/3.98  
% 27.71/3.98  fof(f30,axiom,(
% 27.71/3.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f83,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 27.71/3.98    inference(cnf_transformation,[],[f30])).
% 27.71/3.98  
% 27.71/3.98  fof(f18,axiom,(
% 27.71/3.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f70,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.71/3.98    inference(cnf_transformation,[],[f18])).
% 27.71/3.98  
% 27.71/3.98  fof(f85,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f83,f70])).
% 27.71/3.98  
% 27.71/3.98  fof(f87,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f50,f85,f85])).
% 27.71/3.98  
% 27.71/3.98  fof(f28,axiom,(
% 27.71/3.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f81,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f28])).
% 27.71/3.98  
% 27.71/3.98  fof(f2,axiom,(
% 27.71/3.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f51,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f2])).
% 27.71/3.98  
% 27.71/3.98  fof(f22,axiom,(
% 27.71/3.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f74,plain,(
% 27.71/3.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.71/3.98    inference(cnf_transformation,[],[f22])).
% 27.71/3.98  
% 27.71/3.98  fof(f29,axiom,(
% 27.71/3.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f82,plain,(
% 27.71/3.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 27.71/3.98    inference(cnf_transformation,[],[f29])).
% 27.71/3.98  
% 27.71/3.98  fof(f17,axiom,(
% 27.71/3.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f69,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.71/3.98    inference(cnf_transformation,[],[f17])).
% 27.71/3.98  
% 27.71/3.98  fof(f96,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f69,f70])).
% 27.71/3.98  
% 27.71/3.98  fof(f9,axiom,(
% 27.71/3.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f61,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 27.71/3.98    inference(cnf_transformation,[],[f9])).
% 27.71/3.98  
% 27.71/3.98  fof(f86,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f61,f85,f70])).
% 27.71/3.98  
% 27.71/3.98  fof(f23,axiom,(
% 27.71/3.98    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f75,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f23])).
% 27.71/3.98  
% 27.71/3.98  fof(f25,axiom,(
% 27.71/3.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f47,plain,(
% 27.71/3.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 27.71/3.98    inference(nnf_transformation,[],[f25])).
% 27.71/3.98  
% 27.71/3.98  fof(f77,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f47])).
% 27.71/3.98  
% 27.71/3.98  fof(f24,axiom,(
% 27.71/3.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f76,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.71/3.98    inference(cnf_transformation,[],[f24])).
% 27.71/3.98  
% 27.71/3.98  fof(f99,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f76,f85])).
% 27.71/3.98  
% 27.71/3.98  fof(f8,axiom,(
% 27.71/3.98    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f46,plain,(
% 27.71/3.98    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 27.71/3.98    inference(nnf_transformation,[],[f8])).
% 27.71/3.98  
% 27.71/3.98  fof(f60,plain,(
% 27.71/3.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f46])).
% 27.71/3.98  
% 27.71/3.98  fof(f16,axiom,(
% 27.71/3.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f68,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f16])).
% 27.71/3.98  
% 27.71/3.98  fof(f95,plain,(
% 27.71/3.98    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 27.71/3.98    inference(definition_unfolding,[],[f68,f85])).
% 27.71/3.98  
% 27.71/3.98  fof(f13,axiom,(
% 27.71/3.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f65,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f13])).
% 27.71/3.98  
% 27.71/3.98  fof(f15,axiom,(
% 27.71/3.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f67,plain,(
% 27.71/3.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.71/3.98    inference(cnf_transformation,[],[f15])).
% 27.71/3.98  
% 27.71/3.98  fof(f59,plain,(
% 27.71/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 27.71/3.98    inference(cnf_transformation,[],[f46])).
% 27.71/3.98  
% 27.71/3.98  fof(f31,conjecture,(
% 27.71/3.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 27.71/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.71/3.98  
% 27.71/3.98  fof(f32,negated_conjecture,(
% 27.71/3.98    ~! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 27.71/3.98    inference(negated_conjecture,[],[f31])).
% 27.71/3.98  
% 27.71/3.98  fof(f39,plain,(
% 27.71/3.98    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 27.71/3.98    inference(ennf_transformation,[],[f32])).
% 27.71/3.98  
% 27.71/3.98  fof(f48,plain,(
% 27.71/3.98    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3))),
% 27.71/3.98    introduced(choice_axiom,[])).
% 27.71/3.98  
% 27.71/3.98  fof(f49,plain,(
% 27.71/3.98    ~r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3))),
% 27.71/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f48])).
% 27.71/3.98  
% 27.71/3.98  fof(f84,plain,(
% 27.71/3.98    ~r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3))),
% 27.71/3.98    inference(cnf_transformation,[],[f49])).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 27.71/3.98      inference(cnf_transformation,[],[f87]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_30,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 27.71/3.98      inference(cnf_transformation,[],[f81]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2,plain,
% 27.71/3.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 27.71/3.98      inference(cnf_transformation,[],[f51]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_425,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_1,c_30,c_2]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_23,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f74]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_920,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_30,c_2]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2335,plain,
% 27.71/3.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_23,c_920]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_31,plain,
% 27.71/3.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f82]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1313,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_31,c_30]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1227,plain,
% 27.71/3.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_23,c_2]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1319,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_1313,c_1227]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1802,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2,c_1319]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2393,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2335,c_1802]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_919,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_30,c_2]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2600,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = k5_xboole_0(X2,k1_xboole_0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2393,c_919]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2604,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X0))) = X2 ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_2600,c_23]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_6882,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X1 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_425,c_2604]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_19,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.71/3.98      inference(cnf_transformation,[],[f96]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_0,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 27.71/3.98      inference(cnf_transformation,[],[f86]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_426,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_0,c_30,c_2]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_6721,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))),k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_19,c_426]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_6796,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_6721,c_23,c_31]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7069,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X1 ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_6882,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1876,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1802,c_1802]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_921,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_30,c_2]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2750,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_921,c_1319]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2339,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1802,c_920]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1870,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_30,c_1802]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_6593,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,k5_xboole_0(X3,X0)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2339,c_1870]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7070,plain,
% 27.71/3.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X1,X0),X0)) = X1 ),
% 27.71/3.98      inference(demodulation,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_7069,c_1876,c_2750,c_6593,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2752,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X2,X0))) = X2 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_921,c_1802]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_11939,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),X2),k5_xboole_0(X2,X0)) = k4_xboole_0(X1,X0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_7070,c_2752]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2227,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1876,c_30]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_4699,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_919,c_2227]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1872,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1319,c_1802]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2141,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1872,c_30]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_4360,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2141,c_2141]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_4838,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_4699,c_4360]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2219,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X0,X2) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_919,c_1876]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_6562,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X3)) = k5_xboole_0(X0,k5_xboole_0(X3,X1)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2339,c_2219]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_11966,plain,
% 27.71/3.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k4_xboole_0(X1,X0) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_11939,c_2339,c_4838,c_6562]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_24,plain,
% 27.71/3.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 27.71/3.98      inference(cnf_transformation,[],[f75]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_882,plain,
% 27.71/3.98      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_6746,plain,
% 27.71/3.98      ( r1_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_426,c_882]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7134,plain,
% 27.71/3.98      ( r1_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_6746,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_14691,plain,
% 27.71/3.98      ( r1_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0)))) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1319,c_7134]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_27,plain,
% 27.71/3.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f77]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_879,plain,
% 27.71/3.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_42585,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0)))) = X0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_14691,c_879]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_25,plain,
% 27.71/3.98      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 27.71/3.98      inference(cnf_transformation,[],[f99]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_419,plain,
% 27.71/3.98      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_25,c_30,c_2]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_881,plain,
% 27.71/3.98      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_12328,plain,
% 27.71/3.98      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_881,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_12329,plain,
% 27.71/3.98      ( r1_tarski(X0,k5_xboole_0(k4_xboole_0(X0,X1),X1)) = iProver_top ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_12328,c_2750]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_12333,plain,
% 27.71/3.98      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2,c_12329]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_10,plain,
% 27.71/3.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f60]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_886,plain,
% 27.71/3.98      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_12390,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_12333,c_886]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_105682,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X1,X0))),X0)) = k1_xboole_0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_42585,c_12390]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_18,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.71/3.98      inference(cnf_transformation,[],[f95]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_420,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 27.71/3.98      inference(theory_normalisation,[status(thm)],[c_18,c_30,c_2]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1889,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k5_xboole_0(X1,X2),X3)))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_30,c_420]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2748,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X1) = k5_xboole_0(X2,X0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_921,c_1876]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_8821,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),X1) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_425,c_2748]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_9048,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),X1) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_8821,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_9049,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X1)) = k4_xboole_0(X0,X1) ),
% 27.71/3.98      inference(demodulation,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_9048,c_1319,c_1876,c_2748,c_4838,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_24741,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X2,X1),X0)))) = k4_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_920,c_9049]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2388,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2335,c_1876]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_15,plain,
% 27.71/3.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 27.71/3.98      inference(cnf_transformation,[],[f65]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_883,plain,
% 27.71/3.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_6745,plain,
% 27.71/3.98      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_426,c_883]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7135,plain,
% 27.71/3.98      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1))))) = iProver_top ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_6745,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7136,plain,
% 27.71/3.98      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),X1)) = iProver_top ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_7135,c_2750]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_15026,plain,
% 27.71/3.98      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0),k1_xboole_0)) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2388,c_7136]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_15079,plain,
% 27.71/3.98      ( r1_tarski(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),k1_xboole_0)) = iProver_top ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_15026,c_23]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_17,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f67]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_15080,plain,
% 27.71/3.98      ( r1_tarski(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = iProver_top ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_15079,c_17]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_15404,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_15080,c_886]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_16219,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0))) = k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_15404,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_16262,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_16219,c_15404]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_16263,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_16262,c_2388]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1904,plain,
% 27.71/3.98      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_420,c_883]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_11275,plain,
% 27.71/3.98      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1904,c_886]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_16716,plain,
% 27.71/3.98      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_16263,c_11275]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1806,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_30,c_1319]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_3133,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2393,c_1806]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_3181,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_3133,c_23]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7325,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),X0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_425,c_3181]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7534,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1)))),X0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_7325,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_5630,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),X2) = k5_xboole_0(X0,k5_xboole_0(X3,X1)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_921,c_2219]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7535,plain,
% 27.71/3.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k4_xboole_0(X1,X0) ),
% 27.71/3.98      inference(demodulation,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_7534,c_1876,c_2750,c_4838,c_5630,c_6796]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_18285,plain,
% 27.71/3.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_12390,c_7535]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_11936,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_7070,c_2604]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_18515,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_18285,c_11936]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_18516,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_18515,c_1227]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_59209,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0),k4_xboole_0(k5_xboole_0(X1,X0),X2)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_16716,c_18516]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2351,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X0)) = X2 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_920,c_1872]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7921,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X1))))),k5_xboole_0(X1,X0)) = k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_425,c_2351]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2350,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2) = k5_xboole_0(X1,X0) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_920,c_1876]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2338,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1876,c_920]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2361,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_2338,c_30]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_7767,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X1,X0)) = k5_xboole_0(X3,X2) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2350,c_2361]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_8139,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 27.71/3.98      inference(demodulation,
% 27.71/3.98                [status(thm)],
% 27.71/3.98                [c_7921,c_1319,c_2351,c_6796,c_7767]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_51099,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(X1,X0),X2),k1_xboole_0)) = k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_16716,c_8139]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2555,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_30,c_2393]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2234,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X0)) = k5_xboole_0(X2,X1) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_1876,c_919]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_23178,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),X3) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2555,c_2234]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_2500,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_30,c_2388]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_22379,plain,
% 27.71/3.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2,c_2500]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_23202,plain,
% 27.71/3.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_23178,c_2388,c_4838,c_22379]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_51210,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X0),X2))) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_51099,c_23,c_4838,c_23202]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_59555,plain,
% 27.71/3.98      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X0,X1),X2))) ),
% 27.71/3.98      inference(light_normalisation,[status(thm)],[c_59209,c_2388,c_51210]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_83022,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,X2)),X3) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_1889,c_24741,c_59555]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_83152,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X4,k5_xboole_0(X1,X3))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X2,X3))),X4) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_2141,c_83022]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_83737,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X4,k5_xboole_0(X1,X3)))))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X3,X1)),X4) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_83152,c_2339,c_23202]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_83738,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,k5_xboole_0(X1,X3)),X3))) = k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X3,X1)),X2) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_83737,c_2361,c_4838]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_106013,plain,
% 27.71/3.98      ( k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_105682,c_4838,c_83738]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_11,plain,
% 27.71/3.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 27.71/3.98      inference(cnf_transformation,[],[f59]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_885,plain,
% 27.71/3.98      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_106620,plain,
% 27.71/3.98      ( r1_tarski(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_106013,c_885]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_108984,plain,
% 27.71/3.98      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k5_xboole_0(X0,X1)) = iProver_top ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_11966,c_106620]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1894,plain,
% 27.71/3.98      ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_19,c_420]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_1935,plain,
% 27.71/3.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X0,X1) ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_1894,c_23,c_31]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_108994,plain,
% 27.71/3.98      ( r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = iProver_top ),
% 27.71/3.98      inference(demodulation,[status(thm)],[c_108984,c_1935]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_32,negated_conjecture,
% 27.71/3.98      ( ~ r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) ),
% 27.71/3.98      inference(cnf_transformation,[],[f84]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_876,plain,
% 27.71/3.98      ( r1_tarski(k4_xboole_0(sK2,sK3),k5_xboole_0(sK2,sK3)) != iProver_top ),
% 27.71/3.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 27.71/3.98  
% 27.71/3.98  cnf(c_115256,plain,
% 27.71/3.98      ( $false ),
% 27.71/3.98      inference(superposition,[status(thm)],[c_108994,c_876]) ).
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 27.71/3.98  
% 27.71/3.98  ------                               Statistics
% 27.71/3.98  
% 27.71/3.98  ------ General
% 27.71/3.98  
% 27.71/3.98  abstr_ref_over_cycles:                  0
% 27.71/3.98  abstr_ref_under_cycles:                 0
% 27.71/3.98  gc_basic_clause_elim:                   0
% 27.71/3.98  forced_gc_time:                         0
% 27.71/3.98  parsing_time:                           0.007
% 27.71/3.98  unif_index_cands_time:                  0.
% 27.71/3.98  unif_index_add_time:                    0.
% 27.71/3.98  orderings_time:                         0.
% 27.71/3.98  out_proof_time:                         0.01
% 27.71/3.98  total_time:                             3.079
% 27.71/3.98  num_of_symbols:                         42
% 27.71/3.98  num_of_terms:                           174996
% 27.71/3.98  
% 27.71/3.98  ------ Preprocessing
% 27.71/3.98  
% 27.71/3.98  num_of_splits:                          0
% 27.71/3.98  num_of_split_atoms:                     0
% 27.71/3.98  num_of_reused_defs:                     0
% 27.71/3.98  num_eq_ax_congr_red:                    6
% 27.71/3.98  num_of_sem_filtered_clauses:            1
% 27.71/3.98  num_of_subtypes:                        0
% 27.71/3.98  monotx_restored_types:                  0
% 27.71/3.98  sat_num_of_epr_types:                   0
% 27.71/3.98  sat_num_of_non_cyclic_types:            0
% 27.71/3.98  sat_guarded_non_collapsed_types:        0
% 27.71/3.98  num_pure_diseq_elim:                    0
% 27.71/3.98  simp_replaced_by:                       0
% 27.71/3.98  res_preprocessed:                       116
% 27.71/3.98  prep_upred:                             0
% 27.71/3.98  prep_unflattend:                        23
% 27.71/3.98  smt_new_axioms:                         0
% 27.71/3.98  pred_elim_cands:                        4
% 27.71/3.98  pred_elim:                              0
% 27.71/3.98  pred_elim_cl:                           0
% 27.71/3.98  pred_elim_cycles:                       2
% 27.71/3.98  merged_defs:                            12
% 27.71/3.98  merged_defs_ncl:                        0
% 27.71/3.98  bin_hyper_res:                          12
% 27.71/3.98  prep_cycles:                            3
% 27.71/3.98  pred_elim_time:                         0.002
% 27.71/3.98  splitting_time:                         0.
% 27.71/3.98  sem_filter_time:                        0.
% 27.71/3.98  monotx_time:                            0.
% 27.71/3.98  subtype_inf_time:                       0.
% 27.71/3.98  
% 27.71/3.98  ------ Problem properties
% 27.71/3.98  
% 27.71/3.98  clauses:                                33
% 27.71/3.98  conjectures:                            1
% 27.71/3.98  epr:                                    4
% 27.71/3.98  horn:                                   31
% 27.71/3.98  ground:                                 2
% 27.71/3.98  unary:                                  22
% 27.71/3.98  binary:                                 10
% 27.71/3.98  lits:                                   45
% 27.71/3.98  lits_eq:                                21
% 27.71/3.98  fd_pure:                                0
% 27.71/3.98  fd_pseudo:                              0
% 27.71/3.98  fd_cond:                                0
% 27.71/3.98  fd_pseudo_cond:                         1
% 27.71/3.98  ac_symbols:                             1
% 27.71/3.98  
% 27.71/3.98  ------ Propositional Solver
% 27.71/3.98  
% 27.71/3.98  prop_solver_calls:                      31
% 27.71/3.98  prop_fast_solver_calls:                 805
% 27.71/3.98  smt_solver_calls:                       0
% 27.71/3.98  smt_fast_solver_calls:                  0
% 27.71/3.98  prop_num_of_clauses:                    28388
% 27.71/3.98  prop_preprocess_simplified:             28338
% 27.71/3.98  prop_fo_subsumed:                       1
% 27.71/3.98  prop_solver_time:                       0.
% 27.71/3.98  smt_solver_time:                        0.
% 27.71/3.98  smt_fast_solver_time:                   0.
% 27.71/3.98  prop_fast_solver_time:                  0.
% 27.71/3.98  prop_unsat_core_time:                   0.
% 27.71/3.98  
% 27.71/3.98  ------ QBF
% 27.71/3.98  
% 27.71/3.98  qbf_q_res:                              0
% 27.71/3.98  qbf_num_tautologies:                    0
% 27.71/3.98  qbf_prep_cycles:                        0
% 27.71/3.98  
% 27.71/3.98  ------ BMC1
% 27.71/3.98  
% 27.71/3.98  bmc1_current_bound:                     -1
% 27.71/3.98  bmc1_last_solved_bound:                 -1
% 27.71/3.98  bmc1_unsat_core_size:                   -1
% 27.71/3.98  bmc1_unsat_core_parents_size:           -1
% 27.71/3.98  bmc1_merge_next_fun:                    0
% 27.71/3.98  bmc1_unsat_core_clauses_time:           0.
% 27.71/3.98  
% 27.71/3.98  ------ Instantiation
% 27.71/3.98  
% 27.71/3.98  inst_num_of_clauses:                    4208
% 27.71/3.98  inst_num_in_passive:                    2756
% 27.71/3.98  inst_num_in_active:                     1206
% 27.71/3.98  inst_num_in_unprocessed:                248
% 27.71/3.98  inst_num_of_loops:                      1640
% 27.71/3.98  inst_num_of_learning_restarts:          0
% 27.71/3.98  inst_num_moves_active_passive:          430
% 27.71/3.98  inst_lit_activity:                      0
% 27.71/3.98  inst_lit_activity_moves:                0
% 27.71/3.98  inst_num_tautologies:                   0
% 27.71/3.98  inst_num_prop_implied:                  0
% 27.71/3.98  inst_num_existing_simplified:           0
% 27.71/3.98  inst_num_eq_res_simplified:             0
% 27.71/3.98  inst_num_child_elim:                    0
% 27.71/3.98  inst_num_of_dismatching_blockings:      2997
% 27.71/3.98  inst_num_of_non_proper_insts:           5100
% 27.71/3.98  inst_num_of_duplicates:                 0
% 27.71/3.98  inst_inst_num_from_inst_to_res:         0
% 27.71/3.98  inst_dismatching_checking_time:         0.
% 27.71/3.98  
% 27.71/3.98  ------ Resolution
% 27.71/3.98  
% 27.71/3.98  res_num_of_clauses:                     0
% 27.71/3.98  res_num_in_passive:                     0
% 27.71/3.98  res_num_in_active:                      0
% 27.71/3.98  res_num_of_loops:                       119
% 27.71/3.98  res_forward_subset_subsumed:            798
% 27.71/3.98  res_backward_subset_subsumed:           8
% 27.71/3.98  res_forward_subsumed:                   0
% 27.71/3.98  res_backward_subsumed:                  0
% 27.71/3.98  res_forward_subsumption_resolution:     0
% 27.71/3.98  res_backward_subsumption_resolution:    0
% 27.71/3.98  res_clause_to_clause_subsumption:       227978
% 27.71/3.98  res_orphan_elimination:                 0
% 27.71/3.98  res_tautology_del:                      245
% 27.71/3.98  res_num_eq_res_simplified:              0
% 27.71/3.98  res_num_sel_changes:                    0
% 27.71/3.98  res_moves_from_active_to_pass:          0
% 27.71/3.98  
% 27.71/3.98  ------ Superposition
% 27.71/3.98  
% 27.71/3.98  sup_time_total:                         0.
% 27.71/3.98  sup_time_generating:                    0.
% 27.71/3.98  sup_time_sim_full:                      0.
% 27.71/3.98  sup_time_sim_immed:                     0.
% 27.71/3.98  
% 27.71/3.98  sup_num_of_clauses:                     8474
% 27.71/3.98  sup_num_in_active:                      297
% 27.71/3.98  sup_num_in_passive:                     8177
% 27.71/3.98  sup_num_of_loops:                       326
% 27.71/3.98  sup_fw_superposition:                   29080
% 27.71/3.98  sup_bw_superposition:                   23278
% 27.71/3.98  sup_immediate_simplified:               24527
% 27.71/3.98  sup_given_eliminated:                   12
% 27.71/3.98  comparisons_done:                       0
% 27.71/3.98  comparisons_avoided:                    0
% 27.71/3.98  
% 27.71/3.98  ------ Simplifications
% 27.71/3.98  
% 27.71/3.98  
% 27.71/3.98  sim_fw_subset_subsumed:                 27
% 27.71/3.98  sim_bw_subset_subsumed:                 0
% 27.71/3.98  sim_fw_subsumed:                        3672
% 27.71/3.98  sim_bw_subsumed:                        51
% 27.71/3.98  sim_fw_subsumption_res:                 0
% 27.71/3.98  sim_bw_subsumption_res:                 0
% 27.71/3.98  sim_tautology_del:                      2
% 27.71/3.98  sim_eq_tautology_del:                   4463
% 27.71/3.98  sim_eq_res_simp:                        0
% 27.71/3.98  sim_fw_demodulated:                     19163
% 27.71/3.98  sim_bw_demodulated:                     292
% 27.71/3.98  sim_light_normalised:                   8717
% 27.71/3.98  sim_joinable_taut:                      344
% 27.71/3.98  sim_joinable_simp:                      1
% 27.71/3.98  sim_ac_normalised:                      0
% 27.71/3.98  sim_smt_subsumption:                    0
% 27.71/3.98  
%------------------------------------------------------------------------------
