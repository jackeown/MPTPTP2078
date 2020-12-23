%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:24 EST 2020

% Result     : Theorem 35.18s
% Output     : CNFRefutation 35.18s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 642 expanded)
%              Number of clauses        :   68 ( 308 expanded)
%              Number of leaves         :    9 ( 157 expanded)
%              Depth                    :   17
%              Number of atoms          :   96 ( 751 expanded)
%              Number of equality atoms :   88 ( 624 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f8])).

fof(f11,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f9])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))
   => k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f21,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_5,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_396,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_40,plain,
    ( X0 != X1
    | k3_xboole_0(X0,X2) != X3
    | k2_xboole_0(X3,X1) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_41,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_40])).

cnf(c_6,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_51,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_41,c_6,c_0])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_298,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_320,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_51,c_298])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_597,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_320,c_1])).

cnf(c_1141,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_597,c_5])).

cnf(c_1149,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1141,c_5])).

cnf(c_27063,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k3_xboole_0(X0,k2_xboole_0(X2,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_396,c_1149])).

cnf(c_1144,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X0,X2))) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_597,c_5])).

cnf(c_1146,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1144,c_5])).

cnf(c_584,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_320])).

cnf(c_304,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_51,c_4])).

cnf(c_391,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_304,c_5])).

cnf(c_413,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_391,c_298])).

cnf(c_514,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_413])).

cnf(c_1022,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4,c_584])).

cnf(c_1069,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1022,c_4])).

cnf(c_1095,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_514,c_1069])).

cnf(c_2453,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_584,c_1095])).

cnf(c_301,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_51])).

cnf(c_445,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_301,c_298])).

cnf(c_2483,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2453,c_445])).

cnf(c_27545,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X2) = k3_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_27063,c_1146,c_2483])).

cnf(c_1100,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1069,c_5])).

cnf(c_7,negated_conjecture,
    ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_181013,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_1100,c_7])).

cnf(c_183274,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK2,k2_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_27545,c_181013])).

cnf(c_290,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_449,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X2,X0))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_301,c_290])).

cnf(c_4751,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_5,c_449])).

cnf(c_183277,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK1),sK0) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_183274,c_4751])).

cnf(c_443,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k3_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_301,c_6])).

cnf(c_385,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_298,c_5])).

cnf(c_424,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = X0 ),
    inference(demodulation,[status(thm)],[c_385,c_51])).

cnf(c_1027,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_424,c_584])).

cnf(c_1055,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),X0) ),
    inference(light_normalisation,[status(thm)],[c_1027,c_6])).

cnf(c_336,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(superposition,[status(thm)],[c_290,c_4])).

cnf(c_1056,plain,
    ( k3_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_1055,c_336])).

cnf(c_2337,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_443,c_1056])).

cnf(c_593,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_320,c_5])).

cnf(c_605,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_593,c_51])).

cnf(c_392,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(X0,X2),X3)) = k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_13102,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)),X4) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X3),X4)) ),
    inference(superposition,[status(thm)],[c_605,c_392])).

cnf(c_387,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_13139,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(X3,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_387,c_392])).

cnf(c_13610,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k3_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_13139,c_5,c_387])).

cnf(c_13691,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X2,X3))),X4) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X3),X4)) ),
    inference(demodulation,[status(thm)],[c_13102,c_13610])).

cnf(c_291,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_925,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_413,c_291])).

cnf(c_790,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_301,c_424])).

cnf(c_8235,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_790])).

cnf(c_13693,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_13691,c_925,c_8235])).

cnf(c_67228,plain,
    ( k2_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3))) = k2_xboole_0(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_2337,c_13693])).

cnf(c_440,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_301])).

cnf(c_527,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_413,c_336])).

cnf(c_5368,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_527])).

cnf(c_6152,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_440,c_5368])).

cnf(c_68213,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_67228,c_6152])).

cnf(c_183287,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_183277,c_68213])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:02:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 35.18/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.18/5.00  
% 35.18/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.18/5.00  
% 35.18/5.00  ------  iProver source info
% 35.18/5.00  
% 35.18/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.18/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.18/5.00  git: non_committed_changes: false
% 35.18/5.00  git: last_make_outside_of_git: false
% 35.18/5.00  
% 35.18/5.00  ------ 
% 35.18/5.00  ------ Parsing...
% 35.18/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.18/5.00  
% 35.18/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.18/5.00  
% 35.18/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.18/5.00  
% 35.18/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.18/5.00  ------ Proving...
% 35.18/5.00  ------ Problem Properties 
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  clauses                                 7
% 35.18/5.00  conjectures                             1
% 35.18/5.00  EPR                                     0
% 35.18/5.00  Horn                                    7
% 35.18/5.00  unary                                   7
% 35.18/5.00  binary                                  0
% 35.18/5.00  lits                                    7
% 35.18/5.00  lits eq                                 7
% 35.18/5.00  fd_pure                                 0
% 35.18/5.00  fd_pseudo                               0
% 35.18/5.00  fd_cond                                 0
% 35.18/5.00  fd_pseudo_cond                          0
% 35.18/5.00  AC symbols                              1
% 35.18/5.00  
% 35.18/5.00  ------ Input Options Time Limit: Unbounded
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  ------ Preprocessing...
% 35.18/5.00  
% 35.18/5.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 35.18/5.00  Current options:
% 35.18/5.00  ------ 
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  ------ Proving...
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.18/5.00  
% 35.18/5.00  ------ Proving...
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.18/5.00  
% 35.18/5.00  ------ Proving...
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.18/5.00  
% 35.18/5.00  ------ Proving...
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  % SZS status Theorem for theBenchmark.p
% 35.18/5.00  
% 35.18/5.00   Resolution empty clause
% 35.18/5.00  
% 35.18/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.18/5.00  
% 35.18/5.00  fof(f6,axiom,(
% 35.18/5.00    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 35.18/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.18/5.00  
% 35.18/5.00  fof(f19,plain,(
% 35.18/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 35.18/5.00    inference(cnf_transformation,[],[f6])).
% 35.18/5.00  
% 35.18/5.00  fof(f1,axiom,(
% 35.18/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 35.18/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.18/5.00  
% 35.18/5.00  fof(f14,plain,(
% 35.18/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 35.18/5.00    inference(cnf_transformation,[],[f1])).
% 35.18/5.00  
% 35.18/5.00  fof(f3,axiom,(
% 35.18/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 35.18/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.18/5.00  
% 35.18/5.00  fof(f10,plain,(
% 35.18/5.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 35.18/5.00    inference(ennf_transformation,[],[f3])).
% 35.18/5.00  
% 35.18/5.00  fof(f16,plain,(
% 35.18/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 35.18/5.00    inference(cnf_transformation,[],[f10])).
% 35.18/5.00  
% 35.18/5.00  fof(f4,axiom,(
% 35.18/5.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 35.18/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.18/5.00  
% 35.18/5.00  fof(f17,plain,(
% 35.18/5.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 35.18/5.00    inference(cnf_transformation,[],[f4])).
% 35.18/5.00  
% 35.18/5.00  fof(f7,axiom,(
% 35.18/5.00    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 35.18/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.18/5.00  
% 35.18/5.00  fof(f20,plain,(
% 35.18/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 35.18/5.00    inference(cnf_transformation,[],[f7])).
% 35.18/5.00  
% 35.18/5.00  fof(f5,axiom,(
% 35.18/5.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 35.18/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.18/5.00  
% 35.18/5.00  fof(f18,plain,(
% 35.18/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 35.18/5.00    inference(cnf_transformation,[],[f5])).
% 35.18/5.00  
% 35.18/5.00  fof(f2,axiom,(
% 35.18/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.18/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.18/5.00  
% 35.18/5.00  fof(f15,plain,(
% 35.18/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.18/5.00    inference(cnf_transformation,[],[f2])).
% 35.18/5.00  
% 35.18/5.00  fof(f8,conjecture,(
% 35.18/5.00    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 35.18/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.18/5.00  
% 35.18/5.00  fof(f9,negated_conjecture,(
% 35.18/5.00    ~! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 35.18/5.00    inference(negated_conjecture,[],[f8])).
% 35.18/5.00  
% 35.18/5.00  fof(f11,plain,(
% 35.18/5.00    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 35.18/5.00    inference(ennf_transformation,[],[f9])).
% 35.18/5.00  
% 35.18/5.00  fof(f12,plain,(
% 35.18/5.00    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) => k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 35.18/5.00    introduced(choice_axiom,[])).
% 35.18/5.00  
% 35.18/5.00  fof(f13,plain,(
% 35.18/5.00    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 35.18/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 35.18/5.00  
% 35.18/5.00  fof(f21,plain,(
% 35.18/5.00    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 35.18/5.00    inference(cnf_transformation,[],[f13])).
% 35.18/5.00  
% 35.18/5.00  cnf(c_5,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.18/5.00      inference(cnf_transformation,[],[f19]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_0,plain,
% 35.18/5.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 35.18/5.00      inference(cnf_transformation,[],[f14]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_396,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_2,plain,
% 35.18/5.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 35.18/5.00      inference(cnf_transformation,[],[f16]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_3,plain,
% 35.18/5.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 35.18/5.00      inference(cnf_transformation,[],[f17]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_40,plain,
% 35.18/5.00      ( X0 != X1 | k3_xboole_0(X0,X2) != X3 | k2_xboole_0(X3,X1) = X1 ),
% 35.18/5.00      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_41,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 35.18/5.00      inference(unflattening,[status(thm)],[c_40]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_6,plain,
% 35.18/5.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.18/5.00      inference(cnf_transformation,[],[f20]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_51,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 35.18/5.00      inference(theory_normalisation,[status(thm)],[c_41,c_6,c_0]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_4,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 35.18/5.00      inference(cnf_transformation,[],[f18]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_298,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_320,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_51,c_298]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1,plain,
% 35.18/5.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.18/5.00      inference(cnf_transformation,[],[f15]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_597,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_320,c_1]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1141,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_597,c_5]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1149,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.18/5.00      inference(light_normalisation,[status(thm)],[c_1141,c_5]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_27063,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k3_xboole_0(X0,k2_xboole_0(X2,k3_xboole_0(X0,X1))) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_396,c_1149]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1144,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X0,X2))) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_597,c_5]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1146,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.18/5.00      inference(light_normalisation,[status(thm)],[c_1144,c_5]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_584,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_1,c_320]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_304,plain,
% 35.18/5.00      ( k3_xboole_0(X0,X0) = X0 ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_51,c_4]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_391,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_304,c_5]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_413,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 35.18/5.00      inference(light_normalisation,[status(thm)],[c_391,c_298]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_514,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = X1 ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_1,c_413]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1022,plain,
% 35.18/5.00      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_4,c_584]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1069,plain,
% 35.18/5.00      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
% 35.18/5.00      inference(light_normalisation,[status(thm)],[c_1022,c_4]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1095,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_514,c_1069]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_2453,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X1,X0)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_584,c_1095]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_301,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_1,c_51]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_445,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_301,c_298]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_2483,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 35.18/5.00      inference(light_normalisation,[status(thm)],[c_2453,c_445]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_27545,plain,
% 35.18/5.00      ( k3_xboole_0(k2_xboole_0(X0,X1),X2) = k3_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_27063,c_1146,c_2483]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1100,plain,
% 35.18/5.00      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X2)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_1069,c_5]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_7,negated_conjecture,
% 35.18/5.00      ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
% 35.18/5.00      inference(cnf_transformation,[],[f21]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_181013,plain,
% 35.18/5.00      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,sK1),sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_1100,c_7]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_183274,plain,
% 35.18/5.00      ( k2_xboole_0(sK0,k3_xboole_0(sK2,k2_xboole_0(sK1,sK0))) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_27545,c_181013]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_290,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_449,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X2,X0))) = k2_xboole_0(X1,X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_301,c_290]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_4751,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k3_xboole_0(X1,X2),X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_5,c_449]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_183277,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(sK2,sK1),sK0) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_183274,c_4751]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_443,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k2_xboole_0(k3_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,X2) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_301,c_6]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_385,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_298,c_5]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_424,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = X0 ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_385,c_51]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1027,plain,
% 35.18/5.00      ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X1) = k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_424,c_584]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1055,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X2)),X0) ),
% 35.18/5.00      inference(light_normalisation,[status(thm)],[c_1027,c_6]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_336,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_290,c_4]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_1056,plain,
% 35.18/5.00      ( k3_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = X1 ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_1055,c_336]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_2337,plain,
% 35.18/5.00      ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X2,X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_443,c_1056]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_593,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_320,c_5]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_605,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k3_xboole_0(X0,X1) ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_593,c_51]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_392,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(X0,X2),X3)) = k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_13102,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)),X4) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X3),X4)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_605,c_392]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_387,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_13139,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(X3,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X2,X3))) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_387,c_392]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_13610,plain,
% 35.18/5.00      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k3_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_13139,c_5,c_387]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_13691,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X2,X3))),X4) = k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X3),X4)) ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_13102,c_13610]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_291,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_925,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_413,c_291]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_790,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X1) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_301,c_424]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_8235,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k3_xboole_0(X1,X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_1,c_790]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_13693,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X2,X1),X0) ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_13691,c_925,c_8235]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_67228,plain,
% 35.18/5.00      ( k2_xboole_0(X0,k3_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X2,X3))) = k2_xboole_0(k3_xboole_0(X1,X2),X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_2337,c_13693]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_440,plain,
% 35.18/5.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_4,c_301]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_527,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k3_xboole_0(X0,X1) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_413,c_336]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_5368,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k3_xboole_0(X1,X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_1,c_527]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_6152,plain,
% 35.18/5.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k3_xboole_0(X1,X0) ),
% 35.18/5.00      inference(superposition,[status(thm)],[c_440,c_5368]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_68213,plain,
% 35.18/5.00      ( k2_xboole_0(k3_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 35.18/5.00      inference(demodulation,[status(thm)],[c_67228,c_6152]) ).
% 35.18/5.00  
% 35.18/5.00  cnf(c_183287,plain,
% 35.18/5.00      ( $false ),
% 35.18/5.00      inference(forward_subsumption_resolution,
% 35.18/5.00                [status(thm)],
% 35.18/5.00                [c_183277,c_68213]) ).
% 35.18/5.00  
% 35.18/5.00  
% 35.18/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.18/5.00  
% 35.18/5.00  ------                               Statistics
% 35.18/5.00  
% 35.18/5.00  ------ Selected
% 35.18/5.00  
% 35.18/5.00  total_time:                             4.384
% 35.18/5.00  
%------------------------------------------------------------------------------
