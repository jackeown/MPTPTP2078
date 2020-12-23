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
% DateTime   : Thu Dec  3 11:23:55 EST 2020

% Result     : Theorem 11.87s
% Output     : CNFRefutation 11.87s
% Verified   : 
% Statistics : Number of formulae       :  121 (2110 expanded)
%              Number of clauses        :   88 ( 817 expanded)
%              Number of leaves         :   11 ( 560 expanded)
%              Depth                    :   23
%              Number of atoms          :  153 (2536 expanded)
%              Number of equality atoms :  111 (1970 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f27,f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f28,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f29,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_148,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_85,plain,
    ( X0 != X1
    | k4_xboole_0(X0,k4_xboole_0(X0,X2)) != X3
    | k2_xboole_0(X3,X1) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_86,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_85])).

cnf(c_1365,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_148,c_86])).

cnf(c_227,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_86])).

cnf(c_407,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_227,c_6])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_147,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_130,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_131,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_130,c_5])).

cnf(c_244,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_86,c_131])).

cnf(c_354,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_147,c_244])).

cnf(c_419,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_407,c_7,c_354])).

cnf(c_1002,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_419])).

cnf(c_1452,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_1002])).

cnf(c_1351,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_148])).

cnf(c_361,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_354,c_7])).

cnf(c_160,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_131])).

cnf(c_167,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_160,c_6])).

cnf(c_357,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_354,c_167])).

cnf(c_374,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_361,c_357])).

cnf(c_1421,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1351,c_5,c_374])).

cnf(c_1535,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1452,c_1421])).

cnf(c_1572,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1365,c_1535])).

cnf(c_1573,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1572,c_5,c_6])).

cnf(c_10720,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1573])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_91,plain,
    ( k2_xboole_0(X0,X1) = X1
    | k2_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_10])).

cnf(c_92,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_91])).

cnf(c_362,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_354,c_7])).

cnf(c_867,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_362])).

cnf(c_134,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_141,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_134,c_7])).

cnf(c_791,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_86,c_141])).

cnf(c_855,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_791,c_7,c_374])).

cnf(c_9430,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_867,c_855])).

cnf(c_137,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_7,c_7])).

cnf(c_140,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_137,c_7])).

cnf(c_9477,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9430,c_5,c_7,c_140])).

cnf(c_25070,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_92,c_9477])).

cnf(c_27366,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK1),sK0),k2_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10720,c_25070])).

cnf(c_27648,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK1),sK0),k1_xboole_0),k2_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27366,c_419])).

cnf(c_801,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_92,c_141])).

cnf(c_846,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_801,c_92])).

cnf(c_1133,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_846,c_362])).

cnf(c_1981,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0),k2_xboole_0(X0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1133,c_1002])).

cnf(c_127,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_288,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_127,c_7])).

cnf(c_296,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_288,c_7])).

cnf(c_1996,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1981,c_5,c_7,c_296])).

cnf(c_408,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_227,c_0])).

cnf(c_2474,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK0),k4_xboole_0(sK0,k1_xboole_0)) = k2_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_1996,c_408])).

cnf(c_2479,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK0),sK0) = k2_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_2474,c_5])).

cnf(c_3522,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,X0),sK0) = k2_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_0,c_2479])).

cnf(c_1315,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_148])).

cnf(c_1671,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1315,c_1535])).

cnf(c_1672,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1671,c_5])).

cnf(c_4354,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK0),k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) = k2_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_3522,c_1672])).

cnf(c_2454,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1996])).

cnf(c_4409,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0) = k2_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_4354,c_2454])).

cnf(c_10766,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_1573,c_141])).

cnf(c_10783,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_10766,c_1573])).

cnf(c_27675,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27648,c_7,c_4409,c_10783])).

cnf(c_149,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_28693,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_27675,c_149])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_79,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_80,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_79])).

cnf(c_939,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_80,c_408])).

cnf(c_990,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_939,c_5])).

cnf(c_1321,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),sK0))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) ),
    inference(superposition,[status(thm)],[c_990,c_148])).

cnf(c_1662,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1321,c_1535])).

cnf(c_1663,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))) = sK0 ),
    inference(demodulation,[status(thm)],[c_1662,c_5,c_7])).

cnf(c_11577,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_1663,c_131,c_1996])).

cnf(c_28695,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_28693,c_11577])).

cnf(c_28696,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_28695,c_5])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_96,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_97,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) != sK0 ),
    inference(unflattening,[status(thm)],[c_96])).

cnf(c_98,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != sK0 ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28696,c_98])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:13:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.87/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.87/1.98  
% 11.87/1.98  ------  iProver source info
% 11.87/1.98  
% 11.87/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.87/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.87/1.98  git: non_committed_changes: false
% 11.87/1.98  git: last_make_outside_of_git: false
% 11.87/1.98  
% 11.87/1.98  ------ 
% 11.87/1.98  
% 11.87/1.98  ------ Input Options
% 11.87/1.98  
% 11.87/1.98  --out_options                           all
% 11.87/1.98  --tptp_safe_out                         true
% 11.87/1.98  --problem_path                          ""
% 11.87/1.98  --include_path                          ""
% 11.87/1.98  --clausifier                            res/vclausify_rel
% 11.87/1.98  --clausifier_options                    --mode clausify
% 11.87/1.98  --stdin                                 false
% 11.87/1.98  --stats_out                             all
% 11.87/1.98  
% 11.87/1.98  ------ General Options
% 11.87/1.98  
% 11.87/1.98  --fof                                   false
% 11.87/1.98  --time_out_real                         305.
% 11.87/1.98  --time_out_virtual                      -1.
% 11.87/1.98  --symbol_type_check                     false
% 11.87/1.98  --clausify_out                          false
% 11.87/1.98  --sig_cnt_out                           false
% 11.87/1.98  --trig_cnt_out                          false
% 11.87/1.98  --trig_cnt_out_tolerance                1.
% 11.87/1.98  --trig_cnt_out_sk_spl                   false
% 11.87/1.98  --abstr_cl_out                          false
% 11.87/1.98  
% 11.87/1.98  ------ Global Options
% 11.87/1.98  
% 11.87/1.98  --schedule                              default
% 11.87/1.98  --add_important_lit                     false
% 11.87/1.98  --prop_solver_per_cl                    1000
% 11.87/1.98  --min_unsat_core                        false
% 11.87/1.98  --soft_assumptions                      false
% 11.87/1.98  --soft_lemma_size                       3
% 11.87/1.98  --prop_impl_unit_size                   0
% 11.87/1.98  --prop_impl_unit                        []
% 11.87/1.98  --share_sel_clauses                     true
% 11.87/1.98  --reset_solvers                         false
% 11.87/1.98  --bc_imp_inh                            [conj_cone]
% 11.87/1.98  --conj_cone_tolerance                   3.
% 11.87/1.98  --extra_neg_conj                        none
% 11.87/1.98  --large_theory_mode                     true
% 11.87/1.98  --prolific_symb_bound                   200
% 11.87/1.98  --lt_threshold                          2000
% 11.87/1.98  --clause_weak_htbl                      true
% 11.87/1.98  --gc_record_bc_elim                     false
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing Options
% 11.87/1.98  
% 11.87/1.98  --preprocessing_flag                    true
% 11.87/1.98  --time_out_prep_mult                    0.1
% 11.87/1.98  --splitting_mode                        input
% 11.87/1.98  --splitting_grd                         true
% 11.87/1.98  --splitting_cvd                         false
% 11.87/1.98  --splitting_cvd_svl                     false
% 11.87/1.98  --splitting_nvd                         32
% 11.87/1.98  --sub_typing                            true
% 11.87/1.98  --prep_gs_sim                           true
% 11.87/1.98  --prep_unflatten                        true
% 11.87/1.98  --prep_res_sim                          true
% 11.87/1.98  --prep_upred                            true
% 11.87/1.98  --prep_sem_filter                       exhaustive
% 11.87/1.98  --prep_sem_filter_out                   false
% 11.87/1.98  --pred_elim                             true
% 11.87/1.98  --res_sim_input                         true
% 11.87/1.98  --eq_ax_congr_red                       true
% 11.87/1.98  --pure_diseq_elim                       true
% 11.87/1.98  --brand_transform                       false
% 11.87/1.98  --non_eq_to_eq                          false
% 11.87/1.98  --prep_def_merge                        true
% 11.87/1.98  --prep_def_merge_prop_impl              false
% 11.87/1.98  --prep_def_merge_mbd                    true
% 11.87/1.98  --prep_def_merge_tr_red                 false
% 11.87/1.98  --prep_def_merge_tr_cl                  false
% 11.87/1.98  --smt_preprocessing                     true
% 11.87/1.98  --smt_ac_axioms                         fast
% 11.87/1.98  --preprocessed_out                      false
% 11.87/1.98  --preprocessed_stats                    false
% 11.87/1.98  
% 11.87/1.98  ------ Abstraction refinement Options
% 11.87/1.98  
% 11.87/1.98  --abstr_ref                             []
% 11.87/1.98  --abstr_ref_prep                        false
% 11.87/1.98  --abstr_ref_until_sat                   false
% 11.87/1.98  --abstr_ref_sig_restrict                funpre
% 11.87/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.87/1.98  --abstr_ref_under                       []
% 11.87/1.98  
% 11.87/1.98  ------ SAT Options
% 11.87/1.98  
% 11.87/1.98  --sat_mode                              false
% 11.87/1.98  --sat_fm_restart_options                ""
% 11.87/1.98  --sat_gr_def                            false
% 11.87/1.98  --sat_epr_types                         true
% 11.87/1.98  --sat_non_cyclic_types                  false
% 11.87/1.98  --sat_finite_models                     false
% 11.87/1.98  --sat_fm_lemmas                         false
% 11.87/1.98  --sat_fm_prep                           false
% 11.87/1.98  --sat_fm_uc_incr                        true
% 11.87/1.98  --sat_out_model                         small
% 11.87/1.98  --sat_out_clauses                       false
% 11.87/1.98  
% 11.87/1.98  ------ QBF Options
% 11.87/1.98  
% 11.87/1.98  --qbf_mode                              false
% 11.87/1.98  --qbf_elim_univ                         false
% 11.87/1.98  --qbf_dom_inst                          none
% 11.87/1.98  --qbf_dom_pre_inst                      false
% 11.87/1.98  --qbf_sk_in                             false
% 11.87/1.98  --qbf_pred_elim                         true
% 11.87/1.98  --qbf_split                             512
% 11.87/1.98  
% 11.87/1.98  ------ BMC1 Options
% 11.87/1.98  
% 11.87/1.98  --bmc1_incremental                      false
% 11.87/1.98  --bmc1_axioms                           reachable_all
% 11.87/1.98  --bmc1_min_bound                        0
% 11.87/1.98  --bmc1_max_bound                        -1
% 11.87/1.98  --bmc1_max_bound_default                -1
% 11.87/1.98  --bmc1_symbol_reachability              true
% 11.87/1.98  --bmc1_property_lemmas                  false
% 11.87/1.98  --bmc1_k_induction                      false
% 11.87/1.98  --bmc1_non_equiv_states                 false
% 11.87/1.98  --bmc1_deadlock                         false
% 11.87/1.98  --bmc1_ucm                              false
% 11.87/1.98  --bmc1_add_unsat_core                   none
% 11.87/1.98  --bmc1_unsat_core_children              false
% 11.87/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.87/1.98  --bmc1_out_stat                         full
% 11.87/1.98  --bmc1_ground_init                      false
% 11.87/1.98  --bmc1_pre_inst_next_state              false
% 11.87/1.98  --bmc1_pre_inst_state                   false
% 11.87/1.98  --bmc1_pre_inst_reach_state             false
% 11.87/1.98  --bmc1_out_unsat_core                   false
% 11.87/1.98  --bmc1_aig_witness_out                  false
% 11.87/1.98  --bmc1_verbose                          false
% 11.87/1.98  --bmc1_dump_clauses_tptp                false
% 11.87/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.87/1.98  --bmc1_dump_file                        -
% 11.87/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.87/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.87/1.98  --bmc1_ucm_extend_mode                  1
% 11.87/1.98  --bmc1_ucm_init_mode                    2
% 11.87/1.98  --bmc1_ucm_cone_mode                    none
% 11.87/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.87/1.98  --bmc1_ucm_relax_model                  4
% 11.87/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.87/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.87/1.98  --bmc1_ucm_layered_model                none
% 11.87/1.98  --bmc1_ucm_max_lemma_size               10
% 11.87/1.98  
% 11.87/1.98  ------ AIG Options
% 11.87/1.98  
% 11.87/1.98  --aig_mode                              false
% 11.87/1.98  
% 11.87/1.98  ------ Instantiation Options
% 11.87/1.98  
% 11.87/1.98  --instantiation_flag                    true
% 11.87/1.98  --inst_sos_flag                         false
% 11.87/1.98  --inst_sos_phase                        true
% 11.87/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.87/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.87/1.98  --inst_lit_sel_side                     num_symb
% 11.87/1.98  --inst_solver_per_active                1400
% 11.87/1.98  --inst_solver_calls_frac                1.
% 11.87/1.98  --inst_passive_queue_type               priority_queues
% 11.87/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.87/1.98  --inst_passive_queues_freq              [25;2]
% 11.87/1.98  --inst_dismatching                      true
% 11.87/1.98  --inst_eager_unprocessed_to_passive     true
% 11.87/1.98  --inst_prop_sim_given                   true
% 11.87/1.98  --inst_prop_sim_new                     false
% 11.87/1.98  --inst_subs_new                         false
% 11.87/1.98  --inst_eq_res_simp                      false
% 11.87/1.98  --inst_subs_given                       false
% 11.87/1.98  --inst_orphan_elimination               true
% 11.87/1.98  --inst_learning_loop_flag               true
% 11.87/1.98  --inst_learning_start                   3000
% 11.87/1.98  --inst_learning_factor                  2
% 11.87/1.98  --inst_start_prop_sim_after_learn       3
% 11.87/1.98  --inst_sel_renew                        solver
% 11.87/1.98  --inst_lit_activity_flag                true
% 11.87/1.98  --inst_restr_to_given                   false
% 11.87/1.98  --inst_activity_threshold               500
% 11.87/1.98  --inst_out_proof                        true
% 11.87/1.98  
% 11.87/1.98  ------ Resolution Options
% 11.87/1.98  
% 11.87/1.98  --resolution_flag                       true
% 11.87/1.98  --res_lit_sel                           adaptive
% 11.87/1.98  --res_lit_sel_side                      none
% 11.87/1.98  --res_ordering                          kbo
% 11.87/1.98  --res_to_prop_solver                    active
% 11.87/1.98  --res_prop_simpl_new                    false
% 11.87/1.98  --res_prop_simpl_given                  true
% 11.87/1.98  --res_passive_queue_type                priority_queues
% 11.87/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.87/1.98  --res_passive_queues_freq               [15;5]
% 11.87/1.98  --res_forward_subs                      full
% 11.87/1.98  --res_backward_subs                     full
% 11.87/1.98  --res_forward_subs_resolution           true
% 11.87/1.98  --res_backward_subs_resolution          true
% 11.87/1.98  --res_orphan_elimination                true
% 11.87/1.98  --res_time_limit                        2.
% 11.87/1.98  --res_out_proof                         true
% 11.87/1.98  
% 11.87/1.98  ------ Superposition Options
% 11.87/1.98  
% 11.87/1.98  --superposition_flag                    true
% 11.87/1.98  --sup_passive_queue_type                priority_queues
% 11.87/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.87/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.87/1.98  --demod_completeness_check              fast
% 11.87/1.98  --demod_use_ground                      true
% 11.87/1.98  --sup_to_prop_solver                    passive
% 11.87/1.98  --sup_prop_simpl_new                    true
% 11.87/1.98  --sup_prop_simpl_given                  true
% 11.87/1.98  --sup_fun_splitting                     false
% 11.87/1.98  --sup_smt_interval                      50000
% 11.87/1.98  
% 11.87/1.98  ------ Superposition Simplification Setup
% 11.87/1.98  
% 11.87/1.98  --sup_indices_passive                   []
% 11.87/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.87/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.87/1.98  --sup_full_bw                           [BwDemod]
% 11.87/1.98  --sup_immed_triv                        [TrivRules]
% 11.87/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.87/1.98  --sup_immed_bw_main                     []
% 11.87/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.87/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.87/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.87/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.87/1.98  
% 11.87/1.98  ------ Combination Options
% 11.87/1.98  
% 11.87/1.98  --comb_res_mult                         3
% 11.87/1.98  --comb_sup_mult                         2
% 11.87/1.98  --comb_inst_mult                        10
% 11.87/1.98  
% 11.87/1.98  ------ Debug Options
% 11.87/1.98  
% 11.87/1.98  --dbg_backtrace                         false
% 11.87/1.98  --dbg_dump_prop_clauses                 false
% 11.87/1.98  --dbg_dump_prop_clauses_file            -
% 11.87/1.98  --dbg_out_stat                          false
% 11.87/1.98  ------ Parsing...
% 11.87/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.87/1.98  ------ Proving...
% 11.87/1.98  ------ Problem Properties 
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  clauses                                 10
% 11.87/1.98  conjectures                             0
% 11.87/1.98  EPR                                     0
% 11.87/1.98  Horn                                    10
% 11.87/1.98  unary                                   10
% 11.87/1.98  binary                                  0
% 11.87/1.98  lits                                    10
% 11.87/1.98  lits eq                                 10
% 11.87/1.98  fd_pure                                 0
% 11.87/1.98  fd_pseudo                               0
% 11.87/1.98  fd_cond                                 0
% 11.87/1.98  fd_pseudo_cond                          0
% 11.87/1.98  AC symbols                              0
% 11.87/1.98  
% 11.87/1.98  ------ Schedule UEQ
% 11.87/1.98  
% 11.87/1.98  ------ pure equality problem: resolution off 
% 11.87/1.98  
% 11.87/1.98  ------ Option_UEQ Time Limit: Unbounded
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  ------ 
% 11.87/1.98  Current options:
% 11.87/1.98  ------ 
% 11.87/1.98  
% 11.87/1.98  ------ Input Options
% 11.87/1.98  
% 11.87/1.98  --out_options                           all
% 11.87/1.98  --tptp_safe_out                         true
% 11.87/1.98  --problem_path                          ""
% 11.87/1.98  --include_path                          ""
% 11.87/1.98  --clausifier                            res/vclausify_rel
% 11.87/1.98  --clausifier_options                    --mode clausify
% 11.87/1.98  --stdin                                 false
% 11.87/1.98  --stats_out                             all
% 11.87/1.98  
% 11.87/1.98  ------ General Options
% 11.87/1.98  
% 11.87/1.98  --fof                                   false
% 11.87/1.98  --time_out_real                         305.
% 11.87/1.98  --time_out_virtual                      -1.
% 11.87/1.98  --symbol_type_check                     false
% 11.87/1.98  --clausify_out                          false
% 11.87/1.98  --sig_cnt_out                           false
% 11.87/1.98  --trig_cnt_out                          false
% 11.87/1.98  --trig_cnt_out_tolerance                1.
% 11.87/1.98  --trig_cnt_out_sk_spl                   false
% 11.87/1.98  --abstr_cl_out                          false
% 11.87/1.98  
% 11.87/1.98  ------ Global Options
% 11.87/1.98  
% 11.87/1.98  --schedule                              default
% 11.87/1.98  --add_important_lit                     false
% 11.87/1.98  --prop_solver_per_cl                    1000
% 11.87/1.98  --min_unsat_core                        false
% 11.87/1.98  --soft_assumptions                      false
% 11.87/1.98  --soft_lemma_size                       3
% 11.87/1.98  --prop_impl_unit_size                   0
% 11.87/1.98  --prop_impl_unit                        []
% 11.87/1.98  --share_sel_clauses                     true
% 11.87/1.98  --reset_solvers                         false
% 11.87/1.98  --bc_imp_inh                            [conj_cone]
% 11.87/1.98  --conj_cone_tolerance                   3.
% 11.87/1.98  --extra_neg_conj                        none
% 11.87/1.98  --large_theory_mode                     true
% 11.87/1.98  --prolific_symb_bound                   200
% 11.87/1.98  --lt_threshold                          2000
% 11.87/1.98  --clause_weak_htbl                      true
% 11.87/1.98  --gc_record_bc_elim                     false
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing Options
% 11.87/1.98  
% 11.87/1.98  --preprocessing_flag                    true
% 11.87/1.98  --time_out_prep_mult                    0.1
% 11.87/1.98  --splitting_mode                        input
% 11.87/1.98  --splitting_grd                         true
% 11.87/1.98  --splitting_cvd                         false
% 11.87/1.98  --splitting_cvd_svl                     false
% 11.87/1.98  --splitting_nvd                         32
% 11.87/1.98  --sub_typing                            true
% 11.87/1.98  --prep_gs_sim                           true
% 11.87/1.98  --prep_unflatten                        true
% 11.87/1.98  --prep_res_sim                          true
% 11.87/1.98  --prep_upred                            true
% 11.87/1.98  --prep_sem_filter                       exhaustive
% 11.87/1.98  --prep_sem_filter_out                   false
% 11.87/1.98  --pred_elim                             true
% 11.87/1.98  --res_sim_input                         true
% 11.87/1.98  --eq_ax_congr_red                       true
% 11.87/1.98  --pure_diseq_elim                       true
% 11.87/1.98  --brand_transform                       false
% 11.87/1.98  --non_eq_to_eq                          false
% 11.87/1.98  --prep_def_merge                        true
% 11.87/1.98  --prep_def_merge_prop_impl              false
% 11.87/1.98  --prep_def_merge_mbd                    true
% 11.87/1.98  --prep_def_merge_tr_red                 false
% 11.87/1.98  --prep_def_merge_tr_cl                  false
% 11.87/1.98  --smt_preprocessing                     true
% 11.87/1.98  --smt_ac_axioms                         fast
% 11.87/1.98  --preprocessed_out                      false
% 11.87/1.98  --preprocessed_stats                    false
% 11.87/1.98  
% 11.87/1.98  ------ Abstraction refinement Options
% 11.87/1.98  
% 11.87/1.98  --abstr_ref                             []
% 11.87/1.98  --abstr_ref_prep                        false
% 11.87/1.98  --abstr_ref_until_sat                   false
% 11.87/1.98  --abstr_ref_sig_restrict                funpre
% 11.87/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.87/1.98  --abstr_ref_under                       []
% 11.87/1.98  
% 11.87/1.98  ------ SAT Options
% 11.87/1.98  
% 11.87/1.98  --sat_mode                              false
% 11.87/1.98  --sat_fm_restart_options                ""
% 11.87/1.98  --sat_gr_def                            false
% 11.87/1.98  --sat_epr_types                         true
% 11.87/1.98  --sat_non_cyclic_types                  false
% 11.87/1.98  --sat_finite_models                     false
% 11.87/1.98  --sat_fm_lemmas                         false
% 11.87/1.98  --sat_fm_prep                           false
% 11.87/1.98  --sat_fm_uc_incr                        true
% 11.87/1.98  --sat_out_model                         small
% 11.87/1.98  --sat_out_clauses                       false
% 11.87/1.98  
% 11.87/1.98  ------ QBF Options
% 11.87/1.98  
% 11.87/1.98  --qbf_mode                              false
% 11.87/1.98  --qbf_elim_univ                         false
% 11.87/1.98  --qbf_dom_inst                          none
% 11.87/1.98  --qbf_dom_pre_inst                      false
% 11.87/1.98  --qbf_sk_in                             false
% 11.87/1.98  --qbf_pred_elim                         true
% 11.87/1.98  --qbf_split                             512
% 11.87/1.98  
% 11.87/1.98  ------ BMC1 Options
% 11.87/1.98  
% 11.87/1.98  --bmc1_incremental                      false
% 11.87/1.98  --bmc1_axioms                           reachable_all
% 11.87/1.98  --bmc1_min_bound                        0
% 11.87/1.98  --bmc1_max_bound                        -1
% 11.87/1.98  --bmc1_max_bound_default                -1
% 11.87/1.98  --bmc1_symbol_reachability              true
% 11.87/1.98  --bmc1_property_lemmas                  false
% 11.87/1.98  --bmc1_k_induction                      false
% 11.87/1.98  --bmc1_non_equiv_states                 false
% 11.87/1.98  --bmc1_deadlock                         false
% 11.87/1.98  --bmc1_ucm                              false
% 11.87/1.98  --bmc1_add_unsat_core                   none
% 11.87/1.98  --bmc1_unsat_core_children              false
% 11.87/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.87/1.98  --bmc1_out_stat                         full
% 11.87/1.98  --bmc1_ground_init                      false
% 11.87/1.98  --bmc1_pre_inst_next_state              false
% 11.87/1.98  --bmc1_pre_inst_state                   false
% 11.87/1.98  --bmc1_pre_inst_reach_state             false
% 11.87/1.98  --bmc1_out_unsat_core                   false
% 11.87/1.98  --bmc1_aig_witness_out                  false
% 11.87/1.98  --bmc1_verbose                          false
% 11.87/1.98  --bmc1_dump_clauses_tptp                false
% 11.87/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.87/1.98  --bmc1_dump_file                        -
% 11.87/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.87/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.87/1.98  --bmc1_ucm_extend_mode                  1
% 11.87/1.98  --bmc1_ucm_init_mode                    2
% 11.87/1.98  --bmc1_ucm_cone_mode                    none
% 11.87/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.87/1.98  --bmc1_ucm_relax_model                  4
% 11.87/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.87/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.87/1.98  --bmc1_ucm_layered_model                none
% 11.87/1.98  --bmc1_ucm_max_lemma_size               10
% 11.87/1.98  
% 11.87/1.98  ------ AIG Options
% 11.87/1.98  
% 11.87/1.98  --aig_mode                              false
% 11.87/1.98  
% 11.87/1.98  ------ Instantiation Options
% 11.87/1.98  
% 11.87/1.98  --instantiation_flag                    false
% 11.87/1.98  --inst_sos_flag                         false
% 11.87/1.98  --inst_sos_phase                        true
% 11.87/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.87/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.87/1.98  --inst_lit_sel_side                     num_symb
% 11.87/1.98  --inst_solver_per_active                1400
% 11.87/1.98  --inst_solver_calls_frac                1.
% 11.87/1.98  --inst_passive_queue_type               priority_queues
% 11.87/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.87/1.98  --inst_passive_queues_freq              [25;2]
% 11.87/1.98  --inst_dismatching                      true
% 11.87/1.98  --inst_eager_unprocessed_to_passive     true
% 11.87/1.98  --inst_prop_sim_given                   true
% 11.87/1.98  --inst_prop_sim_new                     false
% 11.87/1.98  --inst_subs_new                         false
% 11.87/1.98  --inst_eq_res_simp                      false
% 11.87/1.98  --inst_subs_given                       false
% 11.87/1.98  --inst_orphan_elimination               true
% 11.87/1.98  --inst_learning_loop_flag               true
% 11.87/1.98  --inst_learning_start                   3000
% 11.87/1.98  --inst_learning_factor                  2
% 11.87/1.98  --inst_start_prop_sim_after_learn       3
% 11.87/1.98  --inst_sel_renew                        solver
% 11.87/1.98  --inst_lit_activity_flag                true
% 11.87/1.98  --inst_restr_to_given                   false
% 11.87/1.98  --inst_activity_threshold               500
% 11.87/1.98  --inst_out_proof                        true
% 11.87/1.98  
% 11.87/1.98  ------ Resolution Options
% 11.87/1.98  
% 11.87/1.98  --resolution_flag                       false
% 11.87/1.98  --res_lit_sel                           adaptive
% 11.87/1.98  --res_lit_sel_side                      none
% 11.87/1.98  --res_ordering                          kbo
% 11.87/1.98  --res_to_prop_solver                    active
% 11.87/1.98  --res_prop_simpl_new                    false
% 11.87/1.98  --res_prop_simpl_given                  true
% 11.87/1.98  --res_passive_queue_type                priority_queues
% 11.87/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.87/1.98  --res_passive_queues_freq               [15;5]
% 11.87/1.98  --res_forward_subs                      full
% 11.87/1.98  --res_backward_subs                     full
% 11.87/1.98  --res_forward_subs_resolution           true
% 11.87/1.98  --res_backward_subs_resolution          true
% 11.87/1.98  --res_orphan_elimination                true
% 11.87/1.98  --res_time_limit                        2.
% 11.87/1.98  --res_out_proof                         true
% 11.87/1.98  
% 11.87/1.98  ------ Superposition Options
% 11.87/1.98  
% 11.87/1.98  --superposition_flag                    true
% 11.87/1.98  --sup_passive_queue_type                priority_queues
% 11.87/1.98  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.87/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.87/1.98  --demod_completeness_check              fast
% 11.87/1.98  --demod_use_ground                      true
% 11.87/1.98  --sup_to_prop_solver                    active
% 11.87/1.98  --sup_prop_simpl_new                    false
% 11.87/1.98  --sup_prop_simpl_given                  false
% 11.87/1.98  --sup_fun_splitting                     true
% 11.87/1.98  --sup_smt_interval                      10000
% 11.87/1.98  
% 11.87/1.98  ------ Superposition Simplification Setup
% 11.87/1.98  
% 11.87/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.87/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.87/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.87/1.98  --sup_full_triv                         [TrivRules]
% 11.87/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.87/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.87/1.98  --sup_immed_triv                        [TrivRules]
% 11.87/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/1.98  --sup_immed_bw_main                     []
% 11.87/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.87/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.87/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.87/1.98  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.87/1.98  
% 11.87/1.98  ------ Combination Options
% 11.87/1.98  
% 11.87/1.98  --comb_res_mult                         1
% 11.87/1.98  --comb_sup_mult                         1
% 11.87/1.98  --comb_inst_mult                        1000000
% 11.87/1.98  
% 11.87/1.98  ------ Debug Options
% 11.87/1.98  
% 11.87/1.98  --dbg_backtrace                         false
% 11.87/1.98  --dbg_dump_prop_clauses                 false
% 11.87/1.98  --dbg_dump_prop_clauses_file            -
% 11.87/1.98  --dbg_out_stat                          false
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  ------ Proving...
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  % SZS status Theorem for theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  fof(f1,axiom,(
% 11.87/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f19,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f1])).
% 11.87/1.98  
% 11.87/1.98  fof(f7,axiom,(
% 11.87/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f25,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f7])).
% 11.87/1.98  
% 11.87/1.98  fof(f2,axiom,(
% 11.87/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f20,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f2])).
% 11.87/1.98  
% 11.87/1.98  fof(f9,axiom,(
% 11.87/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f27,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.87/1.98    inference(cnf_transformation,[],[f9])).
% 11.87/1.98  
% 11.87/1.98  fof(f31,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.87/1.98    inference(definition_unfolding,[],[f20,f27,f27])).
% 11.87/1.98  
% 11.87/1.98  fof(f4,axiom,(
% 11.87/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f14,plain,(
% 11.87/1.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.87/1.98    inference(ennf_transformation,[],[f4])).
% 11.87/1.98  
% 11.87/1.98  fof(f22,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f14])).
% 11.87/1.98  
% 11.87/1.98  fof(f5,axiom,(
% 11.87/1.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f23,plain,(
% 11.87/1.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f5])).
% 11.87/1.98  
% 11.87/1.98  fof(f33,plain,(
% 11.87/1.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 11.87/1.98    inference(definition_unfolding,[],[f23,f27])).
% 11.87/1.98  
% 11.87/1.98  fof(f8,axiom,(
% 11.87/1.98    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f26,plain,(
% 11.87/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f8])).
% 11.87/1.98  
% 11.87/1.98  fof(f6,axiom,(
% 11.87/1.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f24,plain,(
% 11.87/1.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.87/1.98    inference(cnf_transformation,[],[f6])).
% 11.87/1.98  
% 11.87/1.98  fof(f10,conjecture,(
% 11.87/1.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f11,negated_conjecture,(
% 11.87/1.98    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 11.87/1.98    inference(negated_conjecture,[],[f10])).
% 11.87/1.98  
% 11.87/1.98  fof(f15,plain,(
% 11.87/1.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 11.87/1.98    inference(ennf_transformation,[],[f11])).
% 11.87/1.98  
% 11.87/1.98  fof(f16,plain,(
% 11.87/1.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.87/1.98    inference(flattening,[],[f15])).
% 11.87/1.98  
% 11.87/1.98  fof(f17,plain,(
% 11.87/1.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 11.87/1.98    introduced(choice_axiom,[])).
% 11.87/1.98  
% 11.87/1.98  fof(f18,plain,(
% 11.87/1.98    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 11.87/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 11.87/1.98  
% 11.87/1.98  fof(f28,plain,(
% 11.87/1.98    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 11.87/1.98    inference(cnf_transformation,[],[f18])).
% 11.87/1.98  
% 11.87/1.98  fof(f3,axiom,(
% 11.87/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.87/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.87/1.98  
% 11.87/1.98  fof(f12,plain,(
% 11.87/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.87/1.98    inference(unused_predicate_definition_removal,[],[f3])).
% 11.87/1.98  
% 11.87/1.98  fof(f13,plain,(
% 11.87/1.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 11.87/1.98    inference(ennf_transformation,[],[f12])).
% 11.87/1.98  
% 11.87/1.98  fof(f21,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.87/1.98    inference(cnf_transformation,[],[f13])).
% 11.87/1.98  
% 11.87/1.98  fof(f32,plain,(
% 11.87/1.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.87/1.98    inference(definition_unfolding,[],[f21,f27])).
% 11.87/1.98  
% 11.87/1.98  fof(f29,plain,(
% 11.87/1.98    r1_xboole_0(sK0,sK2)),
% 11.87/1.98    inference(cnf_transformation,[],[f18])).
% 11.87/1.98  
% 11.87/1.98  fof(f30,plain,(
% 11.87/1.98    ~r1_tarski(sK0,sK1)),
% 11.87/1.98    inference(cnf_transformation,[],[f18])).
% 11.87/1.98  
% 11.87/1.98  cnf(c_0,plain,
% 11.87/1.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.87/1.98      inference(cnf_transformation,[],[f19]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_6,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.87/1.98      inference(cnf_transformation,[],[f25]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.87/1.98      inference(cnf_transformation,[],[f31]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_148,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_3,plain,
% 11.87/1.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.87/1.98      inference(cnf_transformation,[],[f22]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4,plain,
% 11.87/1.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 11.87/1.98      inference(cnf_transformation,[],[f33]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_85,plain,
% 11.87/1.98      ( X0 != X1
% 11.87/1.98      | k4_xboole_0(X0,k4_xboole_0(X0,X2)) != X3
% 11.87/1.98      | k2_xboole_0(X3,X1) = X1 ),
% 11.87/1.98      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_86,plain,
% 11.87/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
% 11.87/1.98      inference(unflattening,[status(thm)],[c_85]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1365,plain,
% 11.87/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1)))),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_148,c_86]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_227,plain,
% 11.87/1.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1,c_86]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_407,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X1,X1) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_227,c_6]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_7,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.87/1.98      inference(cnf_transformation,[],[f26]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_5,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.87/1.98      inference(cnf_transformation,[],[f24]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_147,plain,
% 11.87/1.98      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_130,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_131,plain,
% 11.87/1.98      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.87/1.98      inference(light_normalisation,[status(thm)],[c_130,c_5]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_244,plain,
% 11.87/1.98      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_86,c_131]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_354,plain,
% 11.87/1.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.87/1.98      inference(light_normalisation,[status(thm)],[c_147,c_244]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_419,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_407,c_7,c_354]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1002,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1,c_419]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1452,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_6,c_1002]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1351,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X0))) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_0,c_148]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_361,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_354,c_7]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_160,plain,
% 11.87/1.98      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_0,c_131]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_167,plain,
% 11.87/1.98      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_160,c_6]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_357,plain,
% 11.87/1.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_354,c_167]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_374,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_361,c_357]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1421,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_1351,c_5,c_374]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1535,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.87/1.98      inference(light_normalisation,[status(thm)],[c_1452,c_1421]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1572,plain,
% 11.87/1.98      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k1_xboole_0)),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_1365,c_1535]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1573,plain,
% 11.87/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_1572,c_5,c_6]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_10720,plain,
% 11.87/1.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_0,c_1573]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_10,negated_conjecture,
% 11.87/1.98      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.87/1.98      inference(cnf_transformation,[],[f28]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_91,plain,
% 11.87/1.98      ( k2_xboole_0(X0,X1) = X1
% 11.87/1.98      | k2_xboole_0(sK1,sK2) != X1
% 11.87/1.98      | sK0 != X0 ),
% 11.87/1.98      inference(resolution_lifted,[status(thm)],[c_3,c_10]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_92,plain,
% 11.87/1.98      ( k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
% 11.87/1.98      inference(unflattening,[status(thm)],[c_91]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_362,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_354,c_7]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_867,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_6,c_362]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_134,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_141,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_134,c_7]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_791,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X0,X2)) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_86,c_141]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_855,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_791,c_7,c_374]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_9430,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_867,c_855]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_137,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_7,c_7]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_140,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_137,c_7]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_9477,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_9430,c_5,c_7,c_140]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_25070,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_92,c_9477]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_27366,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK1),sK0),k2_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_10720,c_25070]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_27648,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK2,sK1),sK0),k1_xboole_0),k2_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_27366,c_419]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_801,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_92,c_141]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_846,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(X0,k2_xboole_0(sK1,sK2)) ),
% 11.87/1.98      inference(light_normalisation,[status(thm)],[c_801,c_92]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1133,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_846,c_362]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1981,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0),k2_xboole_0(X0,sK0)) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1133,c_1002]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_127,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_288,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_127,c_7]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_296,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_288,c_7]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1996,plain,
% 11.87/1.98      ( k4_xboole_0(sK0,k2_xboole_0(X0,sK0)) = k1_xboole_0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_1981,c_5,c_7,c_296]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_408,plain,
% 11.87/1.98      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_227,c_0]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2474,plain,
% 11.87/1.98      ( k2_xboole_0(k2_xboole_0(X0,sK0),k4_xboole_0(sK0,k1_xboole_0)) = k2_xboole_0(X0,sK0) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1996,c_408]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2479,plain,
% 11.87/1.98      ( k2_xboole_0(k2_xboole_0(X0,sK0),sK0) = k2_xboole_0(X0,sK0) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_2474,c_5]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_3522,plain,
% 11.87/1.98      ( k2_xboole_0(k2_xboole_0(sK0,X0),sK0) = k2_xboole_0(X0,sK0) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_0,c_2479]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1315,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_0,c_148]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1671,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_1315,c_1535]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1672,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 11.87/1.98      inference(light_normalisation,[status(thm)],[c_1671,c_5]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4354,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,sK0),k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) = k2_xboole_0(sK0,X0) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_3522,c_1672]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2454,plain,
% 11.87/1.98      ( k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) = k1_xboole_0 ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_0,c_1996]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_4409,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0) = k2_xboole_0(sK0,X0) ),
% 11.87/1.98      inference(light_normalisation,[status(thm)],[c_4354,c_2454]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_10766,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_1573,c_141]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_10783,plain,
% 11.87/1.98      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_10766,c_1573]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_27675,plain,
% 11.87/1.98      ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_27648,c_7,c_4409,c_10783]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_149,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_28693,plain,
% 11.87/1.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_27675,c_149]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_2,plain,
% 11.87/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.87/1.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.87/1.98      inference(cnf_transformation,[],[f32]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_9,negated_conjecture,
% 11.87/1.98      ( r1_xboole_0(sK0,sK2) ),
% 11.87/1.98      inference(cnf_transformation,[],[f29]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_79,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.87/1.98      | sK2 != X1
% 11.87/1.98      | sK0 != X0 ),
% 11.87/1.98      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_80,plain,
% 11.87/1.98      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 11.87/1.98      inference(unflattening,[status(thm)],[c_79]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_939,plain,
% 11.87/1.98      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,sK2) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_80,c_408]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_990,plain,
% 11.87/1.98      ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k4_xboole_0(sK0,sK2) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_939,c_5]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1321,plain,
% 11.87/1.98      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),sK0))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) ),
% 11.87/1.98      inference(superposition,[status(thm)],[c_990,c_148]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1662,plain,
% 11.87/1.98      ( k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_1321,c_1535]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_1663,plain,
% 11.87/1.98      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)))) = sK0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_1662,c_5,c_7]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_11577,plain,
% 11.87/1.98      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_1663,c_131,c_1996]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_28695,plain,
% 11.87/1.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 11.87/1.98      inference(light_normalisation,[status(thm)],[c_28693,c_11577]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_28696,plain,
% 11.87/1.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = sK0 ),
% 11.87/1.98      inference(demodulation,[status(thm)],[c_28695,c_5]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_8,negated_conjecture,
% 11.87/1.98      ( ~ r1_tarski(sK0,sK1) ),
% 11.87/1.98      inference(cnf_transformation,[],[f30]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_96,plain,
% 11.87/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != sK0 | sK1 != X0 ),
% 11.87/1.98      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_97,plain,
% 11.87/1.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) != sK0 ),
% 11.87/1.98      inference(unflattening,[status(thm)],[c_96]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(c_98,plain,
% 11.87/1.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != sK0 ),
% 11.87/1.98      inference(instantiation,[status(thm)],[c_97]) ).
% 11.87/1.98  
% 11.87/1.98  cnf(contradiction,plain,
% 11.87/1.98      ( $false ),
% 11.87/1.98      inference(minisat,[status(thm)],[c_28696,c_98]) ).
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.87/1.98  
% 11.87/1.98  ------                               Statistics
% 11.87/1.98  
% 11.87/1.98  ------ General
% 11.87/1.98  
% 11.87/1.98  abstr_ref_over_cycles:                  0
% 11.87/1.98  abstr_ref_under_cycles:                 0
% 11.87/1.98  gc_basic_clause_elim:                   0
% 11.87/1.98  forced_gc_time:                         0
% 11.87/1.98  parsing_time:                           0.006
% 11.87/1.98  unif_index_cands_time:                  0.
% 11.87/1.98  unif_index_add_time:                    0.
% 11.87/1.98  orderings_time:                         0.
% 11.87/1.98  out_proof_time:                         0.007
% 11.87/1.98  total_time:                             1.358
% 11.87/1.98  num_of_symbols:                         39
% 11.87/1.98  num_of_terms:                           66712
% 11.87/1.98  
% 11.87/1.98  ------ Preprocessing
% 11.87/1.98  
% 11.87/1.98  num_of_splits:                          0
% 11.87/1.98  num_of_split_atoms:                     0
% 11.87/1.98  num_of_reused_defs:                     0
% 11.87/1.98  num_eq_ax_congr_red:                    0
% 11.87/1.98  num_of_sem_filtered_clauses:            0
% 11.87/1.98  num_of_subtypes:                        0
% 11.87/1.98  monotx_restored_types:                  0
% 11.87/1.98  sat_num_of_epr_types:                   0
% 11.87/1.98  sat_num_of_non_cyclic_types:            0
% 11.87/1.98  sat_guarded_non_collapsed_types:        0
% 11.87/1.98  num_pure_diseq_elim:                    0
% 11.87/1.98  simp_replaced_by:                       0
% 11.87/1.98  res_preprocessed:                       35
% 11.87/1.98  prep_upred:                             0
% 11.87/1.98  prep_unflattend:                        7
% 11.87/1.98  smt_new_axioms:                         0
% 11.87/1.98  pred_elim_cands:                        0
% 11.87/1.98  pred_elim:                              2
% 11.87/1.98  pred_elim_cl:                           1
% 11.87/1.98  pred_elim_cycles:                       3
% 11.87/1.98  merged_defs:                            0
% 11.87/1.98  merged_defs_ncl:                        0
% 11.87/1.98  bin_hyper_res:                          0
% 11.87/1.98  prep_cycles:                            3
% 11.87/1.98  pred_elim_time:                         0.001
% 11.87/1.98  splitting_time:                         0.
% 11.87/1.98  sem_filter_time:                        0.
% 11.87/1.98  monotx_time:                            0.
% 11.87/1.98  subtype_inf_time:                       0.
% 11.87/1.98  
% 11.87/1.98  ------ Problem properties
% 11.87/1.98  
% 11.87/1.98  clauses:                                10
% 11.87/1.98  conjectures:                            0
% 11.87/1.98  epr:                                    0
% 11.87/1.98  horn:                                   10
% 11.87/1.98  ground:                                 3
% 11.87/1.98  unary:                                  10
% 11.87/1.98  binary:                                 0
% 11.87/1.98  lits:                                   10
% 11.87/1.98  lits_eq:                                10
% 11.87/1.98  fd_pure:                                0
% 11.87/1.98  fd_pseudo:                              0
% 11.87/1.98  fd_cond:                                0
% 11.87/1.98  fd_pseudo_cond:                         0
% 11.87/1.98  ac_symbols:                             0
% 11.87/1.98  
% 11.87/1.98  ------ Propositional Solver
% 11.87/1.98  
% 11.87/1.98  prop_solver_calls:                      17
% 11.87/1.98  prop_fast_solver_calls:                 92
% 11.87/1.98  smt_solver_calls:                       0
% 11.87/1.98  smt_fast_solver_calls:                  0
% 11.87/1.98  prop_num_of_clauses:                    423
% 11.87/1.98  prop_preprocess_simplified:             530
% 11.87/1.98  prop_fo_subsumed:                       0
% 11.87/1.98  prop_solver_time:                       0.
% 11.87/1.98  smt_solver_time:                        0.
% 11.87/1.98  smt_fast_solver_time:                   0.
% 11.87/1.98  prop_fast_solver_time:                  0.
% 11.87/1.98  prop_unsat_core_time:                   0.
% 11.87/1.98  
% 11.87/1.98  ------ QBF
% 11.87/1.98  
% 11.87/1.98  qbf_q_res:                              0
% 11.87/1.98  qbf_num_tautologies:                    0
% 11.87/1.98  qbf_prep_cycles:                        0
% 11.87/1.98  
% 11.87/1.98  ------ BMC1
% 11.87/1.98  
% 11.87/1.98  bmc1_current_bound:                     -1
% 11.87/1.98  bmc1_last_solved_bound:                 -1
% 11.87/1.98  bmc1_unsat_core_size:                   -1
% 11.87/1.98  bmc1_unsat_core_parents_size:           -1
% 11.87/1.98  bmc1_merge_next_fun:                    0
% 11.87/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.87/1.98  
% 11.87/1.98  ------ Instantiation
% 11.87/1.98  
% 11.87/1.98  inst_num_of_clauses:                    0
% 11.87/1.98  inst_num_in_passive:                    0
% 11.87/1.98  inst_num_in_active:                     0
% 11.87/1.98  inst_num_in_unprocessed:                0
% 11.87/1.98  inst_num_of_loops:                      0
% 11.87/1.98  inst_num_of_learning_restarts:          0
% 11.87/1.98  inst_num_moves_active_passive:          0
% 11.87/1.98  inst_lit_activity:                      0
% 11.87/1.98  inst_lit_activity_moves:                0
% 11.87/1.98  inst_num_tautologies:                   0
% 11.87/1.98  inst_num_prop_implied:                  0
% 11.87/1.98  inst_num_existing_simplified:           0
% 11.87/1.98  inst_num_eq_res_simplified:             0
% 11.87/1.98  inst_num_child_elim:                    0
% 11.87/1.98  inst_num_of_dismatching_blockings:      0
% 11.87/1.98  inst_num_of_non_proper_insts:           0
% 11.87/1.98  inst_num_of_duplicates:                 0
% 11.87/1.98  inst_inst_num_from_inst_to_res:         0
% 11.87/1.98  inst_dismatching_checking_time:         0.
% 11.87/1.98  
% 11.87/1.98  ------ Resolution
% 11.87/1.98  
% 11.87/1.98  res_num_of_clauses:                     0
% 11.87/1.98  res_num_in_passive:                     0
% 11.87/1.98  res_num_in_active:                      0
% 11.87/1.98  res_num_of_loops:                       38
% 11.87/1.98  res_forward_subset_subsumed:            0
% 11.87/1.98  res_backward_subset_subsumed:           0
% 11.87/1.98  res_forward_subsumed:                   0
% 11.87/1.98  res_backward_subsumed:                  0
% 11.87/1.98  res_forward_subsumption_resolution:     0
% 11.87/1.98  res_backward_subsumption_resolution:    0
% 11.87/1.98  res_clause_to_clause_subsumption:       50052
% 11.87/1.98  res_orphan_elimination:                 0
% 11.87/1.98  res_tautology_del:                      0
% 11.87/1.98  res_num_eq_res_simplified:              1
% 11.87/1.98  res_num_sel_changes:                    0
% 11.87/1.98  res_moves_from_active_to_pass:          0
% 11.87/1.98  
% 11.87/1.98  ------ Superposition
% 11.87/1.98  
% 11.87/1.98  sup_time_total:                         0.
% 11.87/1.98  sup_time_generating:                    0.
% 11.87/1.98  sup_time_sim_full:                      0.
% 11.87/1.98  sup_time_sim_immed:                     0.
% 11.87/1.98  
% 11.87/1.98  sup_num_of_clauses:                     4205
% 11.87/1.98  sup_num_in_active:                      178
% 11.87/1.98  sup_num_in_passive:                     4027
% 11.87/1.98  sup_num_of_loops:                       230
% 11.87/1.98  sup_fw_superposition:                   8021
% 11.87/1.98  sup_bw_superposition:                   6672
% 11.87/1.98  sup_immediate_simplified:               9752
% 11.87/1.98  sup_given_eliminated:                   19
% 11.87/1.98  comparisons_done:                       0
% 11.87/1.98  comparisons_avoided:                    0
% 11.87/1.98  
% 11.87/1.98  ------ Simplifications
% 11.87/1.98  
% 11.87/1.98  
% 11.87/1.98  sim_fw_subset_subsumed:                 0
% 11.87/1.98  sim_bw_subset_subsumed:                 0
% 11.87/1.98  sim_fw_subsumed:                        1138
% 11.87/1.98  sim_bw_subsumed:                        179
% 11.87/1.98  sim_fw_subsumption_res:                 0
% 11.87/1.98  sim_bw_subsumption_res:                 0
% 11.87/1.98  sim_tautology_del:                      0
% 11.87/1.98  sim_eq_tautology_del:                   3300
% 11.87/1.98  sim_eq_res_simp:                        0
% 11.87/1.98  sim_fw_demodulated:                     9751
% 11.87/1.98  sim_bw_demodulated:                     211
% 11.87/1.98  sim_light_normalised:                   3789
% 11.87/1.98  sim_joinable_taut:                      0
% 11.87/1.98  sim_joinable_simp:                      0
% 11.87/1.98  sim_ac_normalised:                      0
% 11.87/1.98  sim_smt_subsumption:                    0
% 11.87/1.98  
%------------------------------------------------------------------------------
