%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:48 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  121 (1511 expanded)
%              Number of clauses        :   83 ( 509 expanded)
%              Number of leaves         :   13 ( 380 expanded)
%              Depth                    :   28
%              Number of atoms          :  153 (2541 expanded)
%              Number of equality atoms :  128 (1806 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).

fof(f31,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f29,f29])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f32,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_76,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_6])).

cnf(c_122,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_76])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_123,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_122,c_5])).

cnf(c_269,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_123])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_77,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_13])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_118,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_993,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_77,c_118])).

cnf(c_1240,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_123,c_993])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_78,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_59,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_60,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_59])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_134,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_60,c_9])).

cnf(c_166,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_78,c_134])).

cnf(c_101,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_375,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_166,c_101])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_253,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_367,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_101])).

cnf(c_149,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_403,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_367,c_149])).

cnf(c_442,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_375,c_3,c_76,c_253,c_403])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_54,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_55,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_54])).

cnf(c_133,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_55,c_9])).

cnf(c_164,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_78,c_133])).

cnf(c_218,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_164,c_7])).

cnf(c_275,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_77,c_123])).

cnf(c_601,plain,
    ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_218,c_275])).

cnf(c_1263,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1240,c_442,c_601])).

cnf(c_1264,plain,
    ( sK0 = sK3 ),
    inference(demodulation,[status(thm)],[c_1263,c_6])).

cnf(c_1270,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,sK2))) ),
    inference(demodulation,[status(thm)],[c_1264,c_993])).

cnf(c_1283,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_269,c_1270])).

cnf(c_274,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_123])).

cnf(c_509,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_274,c_5])).

cnf(c_514,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_509,c_3])).

cnf(c_591,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_514,c_218])).

cnf(c_603,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_591,c_164])).

cnf(c_1303,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1283,c_3,c_7,c_76,c_603])).

cnf(c_108,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_1604,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),X0)) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_1303,c_108])).

cnf(c_113,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_60,c_7])).

cnf(c_112,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_55,c_7])).

cnf(c_168,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_112,c_112,c_164])).

cnf(c_170,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_168])).

cnf(c_181,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_170,c_123])).

cnf(c_187,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_113,c_113,c_166,c_181])).

cnf(c_193,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_77,c_187])).

cnf(c_981,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))) = k4_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_193,c_118])).

cnf(c_1141,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_981,c_3,c_7])).

cnf(c_1366,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1141,c_1141,c_1264])).

cnf(c_590,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_218])).

cnf(c_604,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK3,X0) ),
    inference(demodulation,[status(thm)],[c_590,c_218])).

cnf(c_1367,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_1366,c_604])).

cnf(c_1382,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1367,c_1])).

cnf(c_612,plain,
    ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_601,c_5])).

cnf(c_615,plain,
    ( k2_xboole_0(sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_612,c_3])).

cnf(c_227,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_166,c_7])).

cnf(c_785,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_615,c_227])).

cnf(c_786,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_785,c_166])).

cnf(c_1384,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1382,c_786])).

cnf(c_1385,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1384,c_76])).

cnf(c_1613,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X0) = k4_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_1604,c_78,c_1385])).

cnf(c_1614,plain,
    ( k4_xboole_0(sK1,X0) = k4_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_1613,c_6,c_7])).

cnf(c_1996,plain,
    ( k4_xboole_0(sK1,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_1614,c_786])).

cnf(c_102,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_55])).

cnf(c_160,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK1 ),
    inference(superposition,[status(thm)],[c_102,c_9])).

cnf(c_291,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_160,c_78])).

cnf(c_2003,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1996,c_291])).

cnf(c_10,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3838,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_2003,c_10])).

cnf(c_3839,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3838])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.18/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/1.00  
% 3.18/1.00  ------  iProver source info
% 3.18/1.00  
% 3.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/1.00  git: non_committed_changes: false
% 3.18/1.00  git: last_make_outside_of_git: false
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    true
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     num_symb
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       true
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    passive
% 3.18/1.00  --sup_prop_simpl_new                    true
% 3.18/1.00  --sup_prop_simpl_given                  true
% 3.18/1.00  --sup_fun_splitting                     false
% 3.18/1.00  --sup_smt_interval                      50000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   []
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_full_bw                           [BwDemod]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         3
% 3.18/1.00  --comb_sup_mult                         2
% 3.18/1.00  --comb_inst_mult                        10
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  ------ Parsing...
% 3.18/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.18/1.00  ------ Proving...
% 3.18/1.00  ------ Problem Properties 
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  clauses                                 13
% 3.18/1.00  conjectures                             2
% 3.18/1.00  EPR                                     1
% 3.18/1.00  Horn                                    13
% 3.18/1.00  unary                                   13
% 3.18/1.00  binary                                  0
% 3.18/1.00  lits                                    13
% 3.18/1.00  lits eq                                 13
% 3.18/1.00  fd_pure                                 0
% 3.18/1.00  fd_pseudo                               0
% 3.18/1.00  fd_cond                                 0
% 3.18/1.00  fd_pseudo_cond                          0
% 3.18/1.00  AC symbols                              0
% 3.18/1.00  
% 3.18/1.00  ------ Schedule UEQ
% 3.18/1.00  
% 3.18/1.00  ------ pure equality problem: resolution off 
% 3.18/1.00  
% 3.18/1.00  ------ Option_UEQ Time Limit: Unbounded
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  Current options:
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    false
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     num_symb
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       false
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    active
% 3.18/1.00  --sup_prop_simpl_new                    false
% 3.18/1.00  --sup_prop_simpl_given                  false
% 3.18/1.00  --sup_fun_splitting                     true
% 3.18/1.00  --sup_smt_interval                      10000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.18/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         1
% 3.18/1.00  --comb_sup_mult                         1
% 3.18/1.00  --comb_inst_mult                        1000000
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ Proving...
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS status Theorem for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00   Resolution empty clause
% 3.18/1.00  
% 3.18/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  fof(f1,axiom,(
% 3.18/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f20,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f1])).
% 3.18/1.00  
% 3.18/1.00  fof(f8,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f27,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f8])).
% 3.18/1.00  
% 3.18/1.00  fof(f5,axiom,(
% 3.18/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f24,plain,(
% 3.18/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f5])).
% 3.18/1.00  
% 3.18/1.00  fof(f10,axiom,(
% 3.18/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f29,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f10])).
% 3.18/1.00  
% 3.18/1.00  fof(f37,plain,(
% 3.18/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.18/1.00    inference(definition_unfolding,[],[f24,f29])).
% 3.18/1.00  
% 3.18/1.00  fof(f7,axiom,(
% 3.18/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f26,plain,(
% 3.18/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f7])).
% 3.18/1.00  
% 3.18/1.00  fof(f6,axiom,(
% 3.18/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f25,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f6])).
% 3.18/1.00  
% 3.18/1.00  fof(f12,conjecture,(
% 3.18/1.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f13,negated_conjecture,(
% 3.18/1.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.18/1.00    inference(negated_conjecture,[],[f12])).
% 3.18/1.00  
% 3.18/1.00  fof(f16,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 3.18/1.00    inference(ennf_transformation,[],[f13])).
% 3.18/1.00  
% 3.18/1.00  fof(f17,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 3.18/1.00    inference(flattening,[],[f16])).
% 3.18/1.00  
% 3.18/1.00  fof(f18,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f19,plain,(
% 3.18/1.00    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).
% 3.18/1.00  
% 3.18/1.00  fof(f31,plain,(
% 3.18/1.00    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.18/1.00    inference(cnf_transformation,[],[f19])).
% 3.18/1.00  
% 3.18/1.00  fof(f2,axiom,(
% 3.18/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f21,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f2])).
% 3.18/1.00  
% 3.18/1.00  fof(f35,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.18/1.00    inference(definition_unfolding,[],[f21,f29,f29])).
% 3.18/1.00  
% 3.18/1.00  fof(f4,axiom,(
% 3.18/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f23,plain,(
% 3.18/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f4])).
% 3.18/1.00  
% 3.18/1.00  fof(f3,axiom,(
% 3.18/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f14,plain,(
% 3.18/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.18/1.00    inference(unused_predicate_definition_removal,[],[f3])).
% 3.18/1.00  
% 3.18/1.00  fof(f15,plain,(
% 3.18/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 3.18/1.00    inference(ennf_transformation,[],[f14])).
% 3.18/1.00  
% 3.18/1.00  fof(f22,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f15])).
% 3.18/1.00  
% 3.18/1.00  fof(f36,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.18/1.00    inference(definition_unfolding,[],[f22,f29])).
% 3.18/1.00  
% 3.18/1.00  fof(f32,plain,(
% 3.18/1.00    r1_xboole_0(sK2,sK0)),
% 3.18/1.00    inference(cnf_transformation,[],[f19])).
% 3.18/1.00  
% 3.18/1.00  fof(f11,axiom,(
% 3.18/1.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f30,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f11])).
% 3.18/1.00  
% 3.18/1.00  fof(f38,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 3.18/1.00    inference(definition_unfolding,[],[f30,f29])).
% 3.18/1.00  
% 3.18/1.00  fof(f9,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.18/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f28,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f9])).
% 3.18/1.00  
% 3.18/1.00  fof(f33,plain,(
% 3.18/1.00    r1_xboole_0(sK3,sK1)),
% 3.18/1.00    inference(cnf_transformation,[],[f19])).
% 3.18/1.00  
% 3.18/1.00  fof(f34,plain,(
% 3.18/1.00    sK1 != sK2),
% 3.18/1.00    inference(cnf_transformation,[],[f19])).
% 3.18/1.00  
% 3.18/1.00  cnf(c_0,plain,
% 3.18/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f20]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7,plain,
% 3.18/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4,plain,
% 3.18/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6,plain,
% 3.18/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_76,plain,
% 3.18/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_4,c_6]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_122,plain,
% 3.18/1.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_7,c_76]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5,plain,
% 3.18/1.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_123,plain,
% 3.18/1.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_122,c_5]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_269,plain,
% 3.18/1.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_0,c_123]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_13,negated_conjecture,
% 3.18/1.00      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 3.18/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_77,plain,
% 3.18/1.00      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_0,c_13]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1,plain,
% 3.18/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_118,plain,
% 3.18/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_993,plain,
% 3.18/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,sK2))) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_77,c_118]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1240,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_123,c_993]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3,plain,
% 3.18/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_78,plain,
% 3.18/1.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2,plain,
% 3.18/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.18/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12,negated_conjecture,
% 3.18/1.00      ( r1_xboole_0(sK2,sK0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_59,plain,
% 3.18/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.18/1.00      | sK0 != X1
% 3.18/1.00      | sK2 != X0 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_60,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_59]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9,plain,
% 3.18/1.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_134,plain,
% 3.18/1.00      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = sK2 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_60,c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_166,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_78,c_134]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_101,plain,
% 3.18/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_375,plain,
% 3.18/1.00      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_166,c_101]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8,plain,
% 3.18/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_253,plain,
% 3.18/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_367,plain,
% 3.18/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1,c_101]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_149,plain,
% 3.18/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_403,plain,
% 3.18/1.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_367,c_149]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_442,plain,
% 3.18/1.00      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_375,c_3,c_76,c_253,c_403]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_11,negated_conjecture,
% 3.18/1.00      ( r1_xboole_0(sK3,sK1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_54,plain,
% 3.18/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.18/1.00      | sK3 != X0
% 3.18/1.00      | sK1 != X1 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_55,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_54]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_133,plain,
% 3.18/1.00      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = sK3 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_55,c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_164,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_78,c_133]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_218,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_164,c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_275,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_77,c_123]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_601,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,sK0) = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_218,c_275]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1263,plain,
% 3.18/1.00      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0) ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_1240,c_442,c_601]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1264,plain,
% 3.18/1.00      ( sK0 = sK3 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_1263,c_6]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1270,plain,
% 3.18/1.00      ( k4_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k2_xboole_0(sK1,sK3))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,sK2))) ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_1264,c_993]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1283,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_269,c_1270]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_274,plain,
% 3.18/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_9,c_123]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_509,plain,
% 3.18/1.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_274,c_5]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_514,plain,
% 3.18/1.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_509,c_3]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_591,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK3,sK1) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_514,c_218]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_603,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = sK3 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_591,c_164]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1303,plain,
% 3.18/1.00      ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_1283,c_3,c_7,c_76,c_603]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_108,plain,
% 3.18/1.00      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1604,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK1),X0)) = k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1303,c_108]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_113,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_60,c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_112,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_55,c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_168,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_112,c_112,c_164]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_170,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_0,c_168]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_181,plain,
% 3.18/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_170,c_123]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_187,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k1_xboole_0 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_113,c_113,c_166,c_181]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_193,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_77,c_187]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_981,plain,
% 3.18/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))) = k4_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_193,c_118]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1141,plain,
% 3.18/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK2,sK1) ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_981,c_3,c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1366,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,sK1))) = k4_xboole_0(sK2,sK1) ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_1141,c_1141,c_1264]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_590,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_5,c_218]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_604,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK3,X0) ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_590,c_218]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1367,plain,
% 3.18/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK1) ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_1366,c_604]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1382,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK1) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1367,c_1]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_612,plain,
% 3.18/1.00      ( k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_601,c_5]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_615,plain,
% 3.18/1.00      ( k2_xboole_0(sK0,sK3) = sK0 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_612,c_3]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_227,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_166,c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_785,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK0) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_615,c_227]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_786,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_785,c_166]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1384,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_1382,c_786]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1385,plain,
% 3.18/1.00      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_1384,c_76]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1613,plain,
% 3.18/1.00      ( k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X0) = k4_xboole_0(sK2,X0) ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_1604,c_78,c_1385]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1614,plain,
% 3.18/1.00      ( k4_xboole_0(sK1,X0) = k4_xboole_0(sK2,X0) ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_1613,c_6,c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1996,plain,
% 3.18/1.00      ( k4_xboole_0(sK1,sK3) = sK2 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1614,c_786]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_102,plain,
% 3.18/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1,c_55]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_160,plain,
% 3.18/1.00      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK1 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_102,c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_291,plain,
% 3.18/1.00      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_160,c_78]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2003,plain,
% 3.18/1.00      ( sK2 = sK1 ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_1996,c_291]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10,negated_conjecture,
% 3.18/1.00      ( sK1 != sK2 ),
% 3.18/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3838,plain,
% 3.18/1.00      ( sK1 != sK1 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_2003,c_10]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3839,plain,
% 3.18/1.00      ( $false ),
% 3.18/1.00      inference(equality_resolution_simp,[status(thm)],[c_3838]) ).
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  ------                               Statistics
% 3.18/1.00  
% 3.18/1.00  ------ General
% 3.18/1.00  
% 3.18/1.00  abstr_ref_over_cycles:                  0
% 3.18/1.00  abstr_ref_under_cycles:                 0
% 3.18/1.00  gc_basic_clause_elim:                   0
% 3.18/1.00  forced_gc_time:                         0
% 3.18/1.00  parsing_time:                           0.018
% 3.18/1.00  unif_index_cands_time:                  0.
% 3.18/1.00  unif_index_add_time:                    0.
% 3.18/1.00  orderings_time:                         0.
% 3.18/1.00  out_proof_time:                         0.008
% 3.18/1.00  total_time:                             0.325
% 3.18/1.00  num_of_symbols:                         39
% 3.18/1.00  num_of_terms:                           11660
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing
% 3.18/1.00  
% 3.18/1.00  num_of_splits:                          0
% 3.18/1.00  num_of_split_atoms:                     0
% 3.18/1.00  num_of_reused_defs:                     0
% 3.18/1.00  num_eq_ax_congr_red:                    0
% 3.18/1.00  num_of_sem_filtered_clauses:            0
% 3.18/1.00  num_of_subtypes:                        0
% 3.18/1.00  monotx_restored_types:                  0
% 3.18/1.00  sat_num_of_epr_types:                   0
% 3.18/1.00  sat_num_of_non_cyclic_types:            0
% 3.18/1.00  sat_guarded_non_collapsed_types:        0
% 3.18/1.00  num_pure_diseq_elim:                    0
% 3.18/1.00  simp_replaced_by:                       0
% 3.18/1.00  res_preprocessed:                       44
% 3.18/1.00  prep_upred:                             0
% 3.18/1.00  prep_unflattend:                        4
% 3.18/1.00  smt_new_axioms:                         0
% 3.18/1.00  pred_elim_cands:                        0
% 3.18/1.00  pred_elim:                              1
% 3.18/1.00  pred_elim_cl:                           1
% 3.18/1.00  pred_elim_cycles:                       2
% 3.18/1.00  merged_defs:                            0
% 3.18/1.00  merged_defs_ncl:                        0
% 3.18/1.00  bin_hyper_res:                          0
% 3.18/1.00  prep_cycles:                            3
% 3.18/1.00  pred_elim_time:                         0.
% 3.18/1.00  splitting_time:                         0.
% 3.18/1.00  sem_filter_time:                        0.
% 3.18/1.00  monotx_time:                            0.001
% 3.18/1.00  subtype_inf_time:                       0.
% 3.18/1.00  
% 3.18/1.00  ------ Problem properties
% 3.18/1.00  
% 3.18/1.00  clauses:                                13
% 3.18/1.00  conjectures:                            2
% 3.18/1.00  epr:                                    1
% 3.18/1.00  horn:                                   13
% 3.18/1.00  ground:                                 4
% 3.18/1.00  unary:                                  13
% 3.18/1.00  binary:                                 0
% 3.18/1.00  lits:                                   13
% 3.18/1.00  lits_eq:                                13
% 3.18/1.00  fd_pure:                                0
% 3.18/1.00  fd_pseudo:                              0
% 3.18/1.00  fd_cond:                                0
% 3.18/1.00  fd_pseudo_cond:                         0
% 3.18/1.00  ac_symbols:                             0
% 3.18/1.00  
% 3.18/1.00  ------ Propositional Solver
% 3.18/1.00  
% 3.18/1.00  prop_solver_calls:                      17
% 3.18/1.00  prop_fast_solver_calls:                 104
% 3.18/1.00  smt_solver_calls:                       0
% 3.18/1.00  smt_fast_solver_calls:                  0
% 3.18/1.00  prop_num_of_clauses:                    167
% 3.18/1.00  prop_preprocess_simplified:             565
% 3.18/1.00  prop_fo_subsumed:                       0
% 3.18/1.00  prop_solver_time:                       0.
% 3.18/1.00  smt_solver_time:                        0.
% 3.18/1.00  smt_fast_solver_time:                   0.
% 3.18/1.00  prop_fast_solver_time:                  0.
% 3.18/1.00  prop_unsat_core_time:                   0.
% 3.18/1.00  
% 3.18/1.00  ------ QBF
% 3.18/1.00  
% 3.18/1.00  qbf_q_res:                              0
% 3.18/1.00  qbf_num_tautologies:                    0
% 3.18/1.00  qbf_prep_cycles:                        0
% 3.18/1.00  
% 3.18/1.00  ------ BMC1
% 3.18/1.00  
% 3.18/1.00  bmc1_current_bound:                     -1
% 3.18/1.00  bmc1_last_solved_bound:                 -1
% 3.18/1.00  bmc1_unsat_core_size:                   -1
% 3.18/1.00  bmc1_unsat_core_parents_size:           -1
% 3.18/1.00  bmc1_merge_next_fun:                    0
% 3.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation
% 3.18/1.00  
% 3.18/1.00  inst_num_of_clauses:                    0
% 3.18/1.00  inst_num_in_passive:                    0
% 3.18/1.00  inst_num_in_active:                     0
% 3.18/1.00  inst_num_in_unprocessed:                0
% 3.18/1.00  inst_num_of_loops:                      0
% 3.18/1.00  inst_num_of_learning_restarts:          0
% 3.18/1.00  inst_num_moves_active_passive:          0
% 3.18/1.00  inst_lit_activity:                      0
% 3.18/1.00  inst_lit_activity_moves:                0
% 3.18/1.00  inst_num_tautologies:                   0
% 3.18/1.00  inst_num_prop_implied:                  0
% 3.18/1.00  inst_num_existing_simplified:           0
% 3.18/1.00  inst_num_eq_res_simplified:             0
% 3.18/1.00  inst_num_child_elim:                    0
% 3.18/1.00  inst_num_of_dismatching_blockings:      0
% 3.18/1.00  inst_num_of_non_proper_insts:           0
% 3.18/1.00  inst_num_of_duplicates:                 0
% 3.18/1.00  inst_inst_num_from_inst_to_res:         0
% 3.18/1.00  inst_dismatching_checking_time:         0.
% 3.18/1.00  
% 3.18/1.00  ------ Resolution
% 3.18/1.00  
% 3.18/1.00  res_num_of_clauses:                     0
% 3.18/1.00  res_num_in_passive:                     0
% 3.18/1.00  res_num_in_active:                      0
% 3.18/1.00  res_num_of_loops:                       47
% 3.18/1.00  res_forward_subset_subsumed:            0
% 3.18/1.00  res_backward_subset_subsumed:           0
% 3.18/1.00  res_forward_subsumed:                   0
% 3.18/1.00  res_backward_subsumed:                  0
% 3.18/1.00  res_forward_subsumption_resolution:     0
% 3.18/1.00  res_backward_subsumption_resolution:    0
% 3.18/1.00  res_clause_to_clause_subsumption:       5432
% 3.18/1.00  res_orphan_elimination:                 0
% 3.18/1.00  res_tautology_del:                      0
% 3.18/1.00  res_num_eq_res_simplified:              0
% 3.18/1.00  res_num_sel_changes:                    0
% 3.18/1.00  res_moves_from_active_to_pass:          0
% 3.18/1.00  
% 3.18/1.00  ------ Superposition
% 3.18/1.00  
% 3.18/1.00  sup_time_total:                         0.
% 3.18/1.00  sup_time_generating:                    0.
% 3.18/1.00  sup_time_sim_full:                      0.
% 3.18/1.00  sup_time_sim_immed:                     0.
% 3.18/1.00  
% 3.18/1.00  sup_num_of_clauses:                     812
% 3.18/1.00  sup_num_in_active:                      45
% 3.18/1.00  sup_num_in_passive:                     767
% 3.18/1.00  sup_num_of_loops:                       96
% 3.18/1.00  sup_fw_superposition:                   1129
% 3.18/1.00  sup_bw_superposition:                   926
% 3.18/1.00  sup_immediate_simplified:               1174
% 3.18/1.00  sup_given_eliminated:                   7
% 3.18/1.00  comparisons_done:                       0
% 3.18/1.00  comparisons_avoided:                    0
% 3.18/1.00  
% 3.18/1.00  ------ Simplifications
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  sim_fw_subset_subsumed:                 0
% 3.18/1.00  sim_bw_subset_subsumed:                 0
% 3.18/1.00  sim_fw_subsumed:                        166
% 3.18/1.00  sim_bw_subsumed:                        7
% 3.18/1.00  sim_fw_subsumption_res:                 0
% 3.18/1.00  sim_bw_subsumption_res:                 0
% 3.18/1.00  sim_tautology_del:                      0
% 3.18/1.00  sim_eq_tautology_del:                   352
% 3.18/1.00  sim_eq_res_simp:                        0
% 3.18/1.00  sim_fw_demodulated:                     1038
% 3.18/1.00  sim_bw_demodulated:                     82
% 3.18/1.00  sim_light_normalised:                   540
% 3.18/1.00  sim_joinable_taut:                      0
% 3.18/1.00  sim_joinable_simp:                      0
% 3.18/1.00  sim_ac_normalised:                      0
% 3.18/1.00  sim_smt_subsumption:                    0
% 3.18/1.00  
%------------------------------------------------------------------------------
