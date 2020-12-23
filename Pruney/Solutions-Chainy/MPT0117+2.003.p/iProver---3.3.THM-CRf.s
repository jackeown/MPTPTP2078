%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:05 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  128 (1365 expanded)
%              Number of clauses        :   89 ( 416 expanded)
%              Number of leaves         :   12 ( 361 expanded)
%              Depth                    :   26
%              Number of atoms          :  173 (2139 expanded)
%              Number of equality atoms :  127 (1165 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f31,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) ),
    inference(definition_unfolding,[],[f29,f33,f23,f33,f23,f33,f23])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f19,f33,f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f32,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_131,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_132,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_131])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_141,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_142,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_141])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_346,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_1409,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_142,c_346])).

cnf(c_1541,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1409,c_0])).

cnf(c_1863,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2,c_1541])).

cnf(c_1874,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_1863,c_142])).

cnf(c_341,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_1873,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1541,c_341])).

cnf(c_1875,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_1874,c_1873])).

cnf(c_1867,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)))) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1541,c_0])).

cnf(c_1876,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_1875,c_1867])).

cnf(c_1877,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK1,sK0)) = k3_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1876,c_1409])).

cnf(c_2227,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(k3_xboole_0(sK1,sK0),k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0)))) = k3_xboole_0(k3_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1877,c_346])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_390,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_834,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_390,c_0])).

cnf(c_913,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_834,c_0])).

cnf(c_908,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_834])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_115,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_6])).

cnf(c_116,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_115])).

cnf(c_922,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_908,c_7,c_116])).

cnf(c_983,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_913,c_922])).

cnf(c_1311,plain,
    ( k5_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_922,c_390])).

cnf(c_2240,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK0),k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0))) = k3_xboole_0(k3_xboole_0(sK1,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_2227,c_983,c_1311])).

cnf(c_2241,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK0),sK1) = k3_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_2240,c_7,c_1311])).

cnf(c_2467,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,sK1),sK1) = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_2,c_2241])).

cnf(c_2493,plain,
    ( k3_xboole_0(sK1,sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2467,c_142])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_485,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_2,c_8])).

cnf(c_4172,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))))))) = k5_xboole_0(k5_xboole_0(sK0,X0),k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) ),
    inference(superposition,[status(thm)],[c_2493,c_485])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_404,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_142,c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_61,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_146,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_61,c_11])).

cnf(c_147,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_192,plain,
    ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_147,c_142])).

cnf(c_405,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_404,c_192])).

cnf(c_388,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_7])).

cnf(c_391,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_388,c_116])).

cnf(c_406,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_405,c_391])).

cnf(c_594,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_2,c_406])).

cnf(c_600,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_594,c_142])).

cnf(c_4207,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,sK1))))) = k5_xboole_0(k5_xboole_0(sK0,X0),k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_4172,c_600])).

cnf(c_4764,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k5_xboole_0(sK2,sK2)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
    inference(superposition,[status(thm)],[c_132,c_4207])).

cnf(c_136,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_61,c_10])).

cnf(c_137,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_136])).

cnf(c_193,plain,
    ( k5_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_137,c_132])).

cnf(c_403,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_132,c_1])).

cnf(c_407,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_403,c_193])).

cnf(c_408,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK1 ),
    inference(demodulation,[status(thm)],[c_407,c_391])).

cnf(c_670,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_2,c_408])).

cnf(c_676,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_670,c_132])).

cnf(c_1408,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_132,c_346])).

cnf(c_1491,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1408,c_0])).

cnf(c_1640,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2,c_1491])).

cnf(c_1650,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1640,c_132])).

cnf(c_1654,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2,c_1650])).

cnf(c_1664,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1654,c_132])).

cnf(c_1749,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1664,c_341])).

cnf(c_1719,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1664,c_1408])).

cnf(c_1763,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1749,c_1664,c_1719])).

cnf(c_2189,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1763,c_346])).

cnf(c_2202,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK1) ),
    inference(demodulation,[status(thm)],[c_2189,c_983,c_1311])).

cnf(c_2203,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),sK1) = k3_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2202,c_7,c_1311])).

cnf(c_2407,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK1),sK1) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2,c_2203])).

cnf(c_2431,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2407,c_132])).

cnf(c_4786,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_4764,c_142,c_192,c_193,c_676,c_2431])).

cnf(c_400,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_121,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X1)) = k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_61,c_6])).

cnf(c_122,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_121])).

cnf(c_194,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_122,c_116])).

cnf(c_409,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_400,c_116,c_194,c_391])).

cnf(c_4787,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4786,c_116,c_409])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_59,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_126,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | k5_xboole_0(sK0,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_59,c_9])).

cnf(c_127,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4787,c_127])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:10:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.84/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/0.98  
% 3.84/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/0.98  
% 3.84/0.98  ------  iProver source info
% 3.84/0.98  
% 3.84/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.84/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/0.98  git: non_committed_changes: false
% 3.84/0.98  git: last_make_outside_of_git: false
% 3.84/0.98  
% 3.84/0.98  ------ 
% 3.84/0.98  
% 3.84/0.98  ------ Input Options
% 3.84/0.98  
% 3.84/0.98  --out_options                           all
% 3.84/0.98  --tptp_safe_out                         true
% 3.84/0.98  --problem_path                          ""
% 3.84/0.98  --include_path                          ""
% 3.84/0.98  --clausifier                            res/vclausify_rel
% 3.84/0.98  --clausifier_options                    ""
% 3.84/0.98  --stdin                                 false
% 3.84/0.98  --stats_out                             all
% 3.84/0.98  
% 3.84/0.98  ------ General Options
% 3.84/0.98  
% 3.84/0.98  --fof                                   false
% 3.84/0.98  --time_out_real                         305.
% 3.84/0.98  --time_out_virtual                      -1.
% 3.84/0.98  --symbol_type_check                     false
% 3.84/0.98  --clausify_out                          false
% 3.84/0.98  --sig_cnt_out                           false
% 3.84/0.98  --trig_cnt_out                          false
% 3.84/0.98  --trig_cnt_out_tolerance                1.
% 3.84/0.98  --trig_cnt_out_sk_spl                   false
% 3.84/0.98  --abstr_cl_out                          false
% 3.84/0.98  
% 3.84/0.98  ------ Global Options
% 3.84/0.98  
% 3.84/0.98  --schedule                              default
% 3.84/0.98  --add_important_lit                     false
% 3.84/0.98  --prop_solver_per_cl                    1000
% 3.84/0.98  --min_unsat_core                        false
% 3.84/0.98  --soft_assumptions                      false
% 3.84/0.98  --soft_lemma_size                       3
% 3.84/0.98  --prop_impl_unit_size                   0
% 3.84/0.98  --prop_impl_unit                        []
% 3.84/0.98  --share_sel_clauses                     true
% 3.84/0.98  --reset_solvers                         false
% 3.84/0.98  --bc_imp_inh                            [conj_cone]
% 3.84/0.98  --conj_cone_tolerance                   3.
% 3.84/0.98  --extra_neg_conj                        none
% 3.84/0.98  --large_theory_mode                     true
% 3.84/0.98  --prolific_symb_bound                   200
% 3.84/0.98  --lt_threshold                          2000
% 3.84/0.98  --clause_weak_htbl                      true
% 3.84/0.98  --gc_record_bc_elim                     false
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing Options
% 3.84/0.98  
% 3.84/0.98  --preprocessing_flag                    true
% 3.84/0.98  --time_out_prep_mult                    0.1
% 3.84/0.98  --splitting_mode                        input
% 3.84/0.98  --splitting_grd                         true
% 3.84/0.98  --splitting_cvd                         false
% 3.84/0.98  --splitting_cvd_svl                     false
% 3.84/0.98  --splitting_nvd                         32
% 3.84/0.98  --sub_typing                            true
% 3.84/0.98  --prep_gs_sim                           true
% 3.84/0.98  --prep_unflatten                        true
% 3.84/0.98  --prep_res_sim                          true
% 3.84/0.98  --prep_upred                            true
% 3.84/0.98  --prep_sem_filter                       exhaustive
% 3.84/0.98  --prep_sem_filter_out                   false
% 3.84/0.98  --pred_elim                             true
% 3.84/0.98  --res_sim_input                         true
% 3.84/0.98  --eq_ax_congr_red                       true
% 3.84/0.98  --pure_diseq_elim                       true
% 3.84/0.98  --brand_transform                       false
% 3.84/0.98  --non_eq_to_eq                          false
% 3.84/0.98  --prep_def_merge                        true
% 3.84/0.98  --prep_def_merge_prop_impl              false
% 3.84/0.98  --prep_def_merge_mbd                    true
% 3.84/0.98  --prep_def_merge_tr_red                 false
% 3.84/0.98  --prep_def_merge_tr_cl                  false
% 3.84/0.98  --smt_preprocessing                     true
% 3.84/0.98  --smt_ac_axioms                         fast
% 3.84/0.98  --preprocessed_out                      false
% 3.84/0.98  --preprocessed_stats                    false
% 3.84/0.98  
% 3.84/0.98  ------ Abstraction refinement Options
% 3.84/0.98  
% 3.84/0.98  --abstr_ref                             []
% 3.84/0.98  --abstr_ref_prep                        false
% 3.84/0.98  --abstr_ref_until_sat                   false
% 3.84/0.98  --abstr_ref_sig_restrict                funpre
% 3.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.98  --abstr_ref_under                       []
% 3.84/0.98  
% 3.84/0.98  ------ SAT Options
% 3.84/0.98  
% 3.84/0.98  --sat_mode                              false
% 3.84/0.98  --sat_fm_restart_options                ""
% 3.84/0.98  --sat_gr_def                            false
% 3.84/0.98  --sat_epr_types                         true
% 3.84/0.98  --sat_non_cyclic_types                  false
% 3.84/0.98  --sat_finite_models                     false
% 3.84/0.98  --sat_fm_lemmas                         false
% 3.84/0.98  --sat_fm_prep                           false
% 3.84/0.98  --sat_fm_uc_incr                        true
% 3.84/0.98  --sat_out_model                         small
% 3.84/0.98  --sat_out_clauses                       false
% 3.84/0.98  
% 3.84/0.98  ------ QBF Options
% 3.84/0.98  
% 3.84/0.98  --qbf_mode                              false
% 3.84/0.98  --qbf_elim_univ                         false
% 3.84/0.98  --qbf_dom_inst                          none
% 3.84/0.98  --qbf_dom_pre_inst                      false
% 3.84/0.98  --qbf_sk_in                             false
% 3.84/0.98  --qbf_pred_elim                         true
% 3.84/0.98  --qbf_split                             512
% 3.84/0.98  
% 3.84/0.98  ------ BMC1 Options
% 3.84/0.98  
% 3.84/0.98  --bmc1_incremental                      false
% 3.84/0.98  --bmc1_axioms                           reachable_all
% 3.84/0.98  --bmc1_min_bound                        0
% 3.84/0.98  --bmc1_max_bound                        -1
% 3.84/0.98  --bmc1_max_bound_default                -1
% 3.84/0.98  --bmc1_symbol_reachability              true
% 3.84/0.98  --bmc1_property_lemmas                  false
% 3.84/0.98  --bmc1_k_induction                      false
% 3.84/0.98  --bmc1_non_equiv_states                 false
% 3.84/0.98  --bmc1_deadlock                         false
% 3.84/0.98  --bmc1_ucm                              false
% 3.84/0.98  --bmc1_add_unsat_core                   none
% 3.84/0.98  --bmc1_unsat_core_children              false
% 3.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.98  --bmc1_out_stat                         full
% 3.84/0.98  --bmc1_ground_init                      false
% 3.84/0.98  --bmc1_pre_inst_next_state              false
% 3.84/0.98  --bmc1_pre_inst_state                   false
% 3.84/0.98  --bmc1_pre_inst_reach_state             false
% 3.84/0.98  --bmc1_out_unsat_core                   false
% 3.84/0.98  --bmc1_aig_witness_out                  false
% 3.84/0.98  --bmc1_verbose                          false
% 3.84/0.98  --bmc1_dump_clauses_tptp                false
% 3.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.98  --bmc1_dump_file                        -
% 3.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.98  --bmc1_ucm_extend_mode                  1
% 3.84/0.98  --bmc1_ucm_init_mode                    2
% 3.84/0.98  --bmc1_ucm_cone_mode                    none
% 3.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.98  --bmc1_ucm_relax_model                  4
% 3.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.98  --bmc1_ucm_layered_model                none
% 3.84/0.98  --bmc1_ucm_max_lemma_size               10
% 3.84/0.98  
% 3.84/0.98  ------ AIG Options
% 3.84/0.98  
% 3.84/0.98  --aig_mode                              false
% 3.84/0.98  
% 3.84/0.98  ------ Instantiation Options
% 3.84/0.98  
% 3.84/0.98  --instantiation_flag                    true
% 3.84/0.98  --inst_sos_flag                         true
% 3.84/0.98  --inst_sos_phase                        true
% 3.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.98  --inst_lit_sel_side                     num_symb
% 3.84/0.98  --inst_solver_per_active                1400
% 3.84/0.98  --inst_solver_calls_frac                1.
% 3.84/0.98  --inst_passive_queue_type               priority_queues
% 3.84/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.98  --inst_passive_queues_freq              [25;2]
% 3.84/0.98  --inst_dismatching                      true
% 3.84/0.98  --inst_eager_unprocessed_to_passive     true
% 3.84/0.98  --inst_prop_sim_given                   true
% 3.84/0.98  --inst_prop_sim_new                     false
% 3.84/0.98  --inst_subs_new                         false
% 3.84/0.98  --inst_eq_res_simp                      false
% 3.84/0.98  --inst_subs_given                       false
% 3.84/0.98  --inst_orphan_elimination               true
% 3.84/0.98  --inst_learning_loop_flag               true
% 3.84/0.98  --inst_learning_start                   3000
% 3.84/0.98  --inst_learning_factor                  2
% 3.84/0.98  --inst_start_prop_sim_after_learn       3
% 3.84/0.98  --inst_sel_renew                        solver
% 3.84/0.98  --inst_lit_activity_flag                true
% 3.84/0.98  --inst_restr_to_given                   false
% 3.84/0.98  --inst_activity_threshold               500
% 3.84/0.98  --inst_out_proof                        true
% 3.84/0.98  
% 3.84/0.98  ------ Resolution Options
% 3.84/0.98  
% 3.84/0.98  --resolution_flag                       true
% 3.84/0.98  --res_lit_sel                           adaptive
% 3.84/0.98  --res_lit_sel_side                      none
% 3.84/0.98  --res_ordering                          kbo
% 3.84/0.98  --res_to_prop_solver                    active
% 3.84/0.98  --res_prop_simpl_new                    false
% 3.84/0.98  --res_prop_simpl_given                  true
% 3.84/0.98  --res_passive_queue_type                priority_queues
% 3.84/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.98  --res_passive_queues_freq               [15;5]
% 3.84/0.98  --res_forward_subs                      full
% 3.84/0.98  --res_backward_subs                     full
% 3.84/0.98  --res_forward_subs_resolution           true
% 3.84/0.98  --res_backward_subs_resolution          true
% 3.84/0.98  --res_orphan_elimination                true
% 3.84/0.98  --res_time_limit                        2.
% 3.84/0.98  --res_out_proof                         true
% 3.84/0.98  
% 3.84/0.98  ------ Superposition Options
% 3.84/0.98  
% 3.84/0.98  --superposition_flag                    true
% 3.84/0.98  --sup_passive_queue_type                priority_queues
% 3.84/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.98  --demod_completeness_check              fast
% 3.84/0.98  --demod_use_ground                      true
% 3.84/0.98  --sup_to_prop_solver                    passive
% 3.84/0.98  --sup_prop_simpl_new                    true
% 3.84/0.98  --sup_prop_simpl_given                  true
% 3.84/0.98  --sup_fun_splitting                     true
% 3.84/0.98  --sup_smt_interval                      50000
% 3.84/0.98  
% 3.84/0.98  ------ Superposition Simplification Setup
% 3.84/0.98  
% 3.84/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/0.98  --sup_immed_triv                        [TrivRules]
% 3.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.98  --sup_immed_bw_main                     []
% 3.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.98  --sup_input_bw                          []
% 3.84/0.98  
% 3.84/0.98  ------ Combination Options
% 3.84/0.98  
% 3.84/0.98  --comb_res_mult                         3
% 3.84/0.98  --comb_sup_mult                         2
% 3.84/0.98  --comb_inst_mult                        10
% 3.84/0.98  
% 3.84/0.98  ------ Debug Options
% 3.84/0.98  
% 3.84/0.98  --dbg_backtrace                         false
% 3.84/0.98  --dbg_dump_prop_clauses                 false
% 3.84/0.98  --dbg_dump_prop_clauses_file            -
% 3.84/0.98  --dbg_out_stat                          false
% 3.84/0.98  ------ Parsing...
% 3.84/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.84/0.98  ------ Proving...
% 3.84/0.98  ------ Problem Properties 
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  clauses                                 16
% 3.84/0.98  conjectures                             0
% 3.84/0.98  EPR                                     0
% 3.84/0.98  Horn                                    16
% 3.84/0.98  unary                                   13
% 3.84/0.98  binary                                  3
% 3.84/0.98  lits                                    19
% 3.84/0.98  lits eq                                 19
% 3.84/0.98  fd_pure                                 0
% 3.84/0.98  fd_pseudo                               0
% 3.84/0.98  fd_cond                                 0
% 3.84/0.98  fd_pseudo_cond                          0
% 3.84/0.98  AC symbols                              0
% 3.84/0.98  
% 3.84/0.98  ------ Schedule dynamic 5 is on 
% 3.84/0.98  
% 3.84/0.98  ------ no conjectures: strip conj schedule 
% 3.84/0.98  
% 3.84/0.98  ------ pure equality problem: resolution off 
% 3.84/0.98  
% 3.84/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  ------ 
% 3.84/0.98  Current options:
% 3.84/0.98  ------ 
% 3.84/0.98  
% 3.84/0.98  ------ Input Options
% 3.84/0.98  
% 3.84/0.98  --out_options                           all
% 3.84/0.98  --tptp_safe_out                         true
% 3.84/0.98  --problem_path                          ""
% 3.84/0.98  --include_path                          ""
% 3.84/0.98  --clausifier                            res/vclausify_rel
% 3.84/0.98  --clausifier_options                    ""
% 3.84/0.98  --stdin                                 false
% 3.84/0.98  --stats_out                             all
% 3.84/0.98  
% 3.84/0.98  ------ General Options
% 3.84/0.98  
% 3.84/0.98  --fof                                   false
% 3.84/0.98  --time_out_real                         305.
% 3.84/0.98  --time_out_virtual                      -1.
% 3.84/0.98  --symbol_type_check                     false
% 3.84/0.98  --clausify_out                          false
% 3.84/0.98  --sig_cnt_out                           false
% 3.84/0.98  --trig_cnt_out                          false
% 3.84/0.98  --trig_cnt_out_tolerance                1.
% 3.84/0.98  --trig_cnt_out_sk_spl                   false
% 3.84/0.98  --abstr_cl_out                          false
% 3.84/0.98  
% 3.84/0.98  ------ Global Options
% 3.84/0.98  
% 3.84/0.98  --schedule                              default
% 3.84/0.98  --add_important_lit                     false
% 3.84/0.98  --prop_solver_per_cl                    1000
% 3.84/0.98  --min_unsat_core                        false
% 3.84/0.98  --soft_assumptions                      false
% 3.84/0.98  --soft_lemma_size                       3
% 3.84/0.98  --prop_impl_unit_size                   0
% 3.84/0.98  --prop_impl_unit                        []
% 3.84/0.98  --share_sel_clauses                     true
% 3.84/0.98  --reset_solvers                         false
% 3.84/0.98  --bc_imp_inh                            [conj_cone]
% 3.84/0.98  --conj_cone_tolerance                   3.
% 3.84/0.98  --extra_neg_conj                        none
% 3.84/0.98  --large_theory_mode                     true
% 3.84/0.98  --prolific_symb_bound                   200
% 3.84/0.98  --lt_threshold                          2000
% 3.84/0.98  --clause_weak_htbl                      true
% 3.84/0.98  --gc_record_bc_elim                     false
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing Options
% 3.84/0.98  
% 3.84/0.98  --preprocessing_flag                    true
% 3.84/0.98  --time_out_prep_mult                    0.1
% 3.84/0.98  --splitting_mode                        input
% 3.84/0.98  --splitting_grd                         true
% 3.84/0.98  --splitting_cvd                         false
% 3.84/0.98  --splitting_cvd_svl                     false
% 3.84/0.98  --splitting_nvd                         32
% 3.84/0.98  --sub_typing                            true
% 3.84/0.98  --prep_gs_sim                           true
% 3.84/0.98  --prep_unflatten                        true
% 3.84/0.98  --prep_res_sim                          true
% 3.84/0.98  --prep_upred                            true
% 3.84/0.98  --prep_sem_filter                       exhaustive
% 3.84/0.98  --prep_sem_filter_out                   false
% 3.84/0.98  --pred_elim                             true
% 3.84/0.98  --res_sim_input                         true
% 3.84/0.98  --eq_ax_congr_red                       true
% 3.84/0.98  --pure_diseq_elim                       true
% 3.84/0.98  --brand_transform                       false
% 3.84/0.98  --non_eq_to_eq                          false
% 3.84/0.98  --prep_def_merge                        true
% 3.84/0.98  --prep_def_merge_prop_impl              false
% 3.84/0.98  --prep_def_merge_mbd                    true
% 3.84/0.98  --prep_def_merge_tr_red                 false
% 3.84/0.98  --prep_def_merge_tr_cl                  false
% 3.84/0.98  --smt_preprocessing                     true
% 3.84/0.98  --smt_ac_axioms                         fast
% 3.84/0.98  --preprocessed_out                      false
% 3.84/0.98  --preprocessed_stats                    false
% 3.84/0.98  
% 3.84/0.98  ------ Abstraction refinement Options
% 3.84/0.98  
% 3.84/0.98  --abstr_ref                             []
% 3.84/0.98  --abstr_ref_prep                        false
% 3.84/0.98  --abstr_ref_until_sat                   false
% 3.84/0.98  --abstr_ref_sig_restrict                funpre
% 3.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.98  --abstr_ref_under                       []
% 3.84/0.98  
% 3.84/0.98  ------ SAT Options
% 3.84/0.98  
% 3.84/0.98  --sat_mode                              false
% 3.84/0.98  --sat_fm_restart_options                ""
% 3.84/0.98  --sat_gr_def                            false
% 3.84/0.98  --sat_epr_types                         true
% 3.84/0.98  --sat_non_cyclic_types                  false
% 3.84/0.98  --sat_finite_models                     false
% 3.84/0.98  --sat_fm_lemmas                         false
% 3.84/0.98  --sat_fm_prep                           false
% 3.84/0.98  --sat_fm_uc_incr                        true
% 3.84/0.98  --sat_out_model                         small
% 3.84/0.98  --sat_out_clauses                       false
% 3.84/0.98  
% 3.84/0.98  ------ QBF Options
% 3.84/0.98  
% 3.84/0.98  --qbf_mode                              false
% 3.84/0.98  --qbf_elim_univ                         false
% 3.84/0.98  --qbf_dom_inst                          none
% 3.84/0.98  --qbf_dom_pre_inst                      false
% 3.84/0.98  --qbf_sk_in                             false
% 3.84/0.98  --qbf_pred_elim                         true
% 3.84/0.98  --qbf_split                             512
% 3.84/0.98  
% 3.84/0.98  ------ BMC1 Options
% 3.84/0.98  
% 3.84/0.98  --bmc1_incremental                      false
% 3.84/0.98  --bmc1_axioms                           reachable_all
% 3.84/0.98  --bmc1_min_bound                        0
% 3.84/0.98  --bmc1_max_bound                        -1
% 3.84/0.98  --bmc1_max_bound_default                -1
% 3.84/0.98  --bmc1_symbol_reachability              true
% 3.84/0.98  --bmc1_property_lemmas                  false
% 3.84/0.98  --bmc1_k_induction                      false
% 3.84/0.98  --bmc1_non_equiv_states                 false
% 3.84/0.98  --bmc1_deadlock                         false
% 3.84/0.98  --bmc1_ucm                              false
% 3.84/0.98  --bmc1_add_unsat_core                   none
% 3.84/0.98  --bmc1_unsat_core_children              false
% 3.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.98  --bmc1_out_stat                         full
% 3.84/0.98  --bmc1_ground_init                      false
% 3.84/0.98  --bmc1_pre_inst_next_state              false
% 3.84/0.98  --bmc1_pre_inst_state                   false
% 3.84/0.98  --bmc1_pre_inst_reach_state             false
% 3.84/0.98  --bmc1_out_unsat_core                   false
% 3.84/0.98  --bmc1_aig_witness_out                  false
% 3.84/0.98  --bmc1_verbose                          false
% 3.84/0.98  --bmc1_dump_clauses_tptp                false
% 3.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.98  --bmc1_dump_file                        -
% 3.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.98  --bmc1_ucm_extend_mode                  1
% 3.84/0.98  --bmc1_ucm_init_mode                    2
% 3.84/0.98  --bmc1_ucm_cone_mode                    none
% 3.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.98  --bmc1_ucm_relax_model                  4
% 3.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.98  --bmc1_ucm_layered_model                none
% 3.84/0.98  --bmc1_ucm_max_lemma_size               10
% 3.84/0.98  
% 3.84/0.98  ------ AIG Options
% 3.84/0.98  
% 3.84/0.98  --aig_mode                              false
% 3.84/0.98  
% 3.84/0.98  ------ Instantiation Options
% 3.84/0.98  
% 3.84/0.98  --instantiation_flag                    true
% 3.84/0.98  --inst_sos_flag                         true
% 3.84/0.98  --inst_sos_phase                        true
% 3.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.98  --inst_lit_sel_side                     none
% 3.84/0.98  --inst_solver_per_active                1400
% 3.84/0.98  --inst_solver_calls_frac                1.
% 3.84/0.98  --inst_passive_queue_type               priority_queues
% 3.84/0.98  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 3.84/0.98  --inst_passive_queues_freq              [25;2]
% 3.84/0.98  --inst_dismatching                      true
% 3.84/0.98  --inst_eager_unprocessed_to_passive     true
% 3.84/0.98  --inst_prop_sim_given                   true
% 3.84/0.98  --inst_prop_sim_new                     false
% 3.84/0.98  --inst_subs_new                         false
% 3.84/0.98  --inst_eq_res_simp                      false
% 3.84/0.98  --inst_subs_given                       false
% 3.84/0.98  --inst_orphan_elimination               true
% 3.84/0.98  --inst_learning_loop_flag               true
% 3.84/0.98  --inst_learning_start                   3000
% 3.84/0.98  --inst_learning_factor                  2
% 3.84/0.98  --inst_start_prop_sim_after_learn       3
% 3.84/0.98  --inst_sel_renew                        solver
% 3.84/0.98  --inst_lit_activity_flag                true
% 3.84/0.98  --inst_restr_to_given                   false
% 3.84/0.98  --inst_activity_threshold               500
% 3.84/0.98  --inst_out_proof                        true
% 3.84/0.98  
% 3.84/0.98  ------ Resolution Options
% 3.84/0.98  
% 3.84/0.98  --resolution_flag                       false
% 3.84/0.98  --res_lit_sel                           adaptive
% 3.84/0.98  --res_lit_sel_side                      none
% 3.84/0.98  --res_ordering                          kbo
% 3.84/0.98  --res_to_prop_solver                    active
% 3.84/0.98  --res_prop_simpl_new                    false
% 3.84/0.98  --res_prop_simpl_given                  true
% 3.84/0.98  --res_passive_queue_type                priority_queues
% 3.84/0.98  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 3.84/0.98  --res_passive_queues_freq               [15;5]
% 3.84/0.98  --res_forward_subs                      full
% 3.84/0.98  --res_backward_subs                     full
% 3.84/0.98  --res_forward_subs_resolution           true
% 3.84/0.98  --res_backward_subs_resolution          true
% 3.84/0.98  --res_orphan_elimination                true
% 3.84/0.98  --res_time_limit                        2.
% 3.84/0.98  --res_out_proof                         true
% 3.84/0.98  
% 3.84/0.98  ------ Superposition Options
% 3.84/0.98  
% 3.84/0.98  --superposition_flag                    true
% 3.84/0.98  --sup_passive_queue_type                priority_queues
% 3.84/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.98  --demod_completeness_check              fast
% 3.84/0.98  --demod_use_ground                      true
% 3.84/0.98  --sup_to_prop_solver                    passive
% 3.84/0.98  --sup_prop_simpl_new                    true
% 3.84/0.98  --sup_prop_simpl_given                  true
% 3.84/0.98  --sup_fun_splitting                     true
% 3.84/0.98  --sup_smt_interval                      50000
% 3.84/0.98  
% 3.84/0.98  ------ Superposition Simplification Setup
% 3.84/0.98  
% 3.84/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.84/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.84/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.84/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.84/0.98  --sup_immed_triv                        [TrivRules]
% 3.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.98  --sup_immed_bw_main                     []
% 3.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.98  --sup_input_bw                          []
% 3.84/0.98  
% 3.84/0.98  ------ Combination Options
% 3.84/0.98  
% 3.84/0.98  --comb_res_mult                         3
% 3.84/0.98  --comb_sup_mult                         2
% 3.84/0.98  --comb_inst_mult                        10
% 3.84/0.98  
% 3.84/0.98  ------ Debug Options
% 3.84/0.98  
% 3.84/0.98  --dbg_backtrace                         false
% 3.84/0.98  --dbg_dump_prop_clauses                 false
% 3.84/0.98  --dbg_dump_prop_clauses_file            -
% 3.84/0.98  --dbg_out_stat                          false
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  ------ Proving...
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  % SZS status Theorem for theBenchmark.p
% 3.84/0.98  
% 3.84/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/0.98  
% 3.84/0.98  fof(f5,axiom,(
% 3.84/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f13,plain,(
% 3.84/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.84/0.98    inference(ennf_transformation,[],[f5])).
% 3.84/0.98  
% 3.84/0.98  fof(f24,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f13])).
% 3.84/0.98  
% 3.84/0.98  fof(f11,conjecture,(
% 3.84/0.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f12,negated_conjecture,(
% 3.84/0.98    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 3.84/0.98    inference(negated_conjecture,[],[f11])).
% 3.84/0.98  
% 3.84/0.98  fof(f14,plain,(
% 3.84/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 3.84/0.98    inference(ennf_transformation,[],[f12])).
% 3.84/0.98  
% 3.84/0.98  fof(f15,plain,(
% 3.84/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 3.84/0.98    inference(flattening,[],[f14])).
% 3.84/0.98  
% 3.84/0.98  fof(f17,plain,(
% 3.84/0.98    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 3.84/0.98    introduced(choice_axiom,[])).
% 3.84/0.98  
% 3.84/0.98  fof(f18,plain,(
% 3.84/0.98    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 3.84/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 3.84/0.98  
% 3.84/0.98  fof(f31,plain,(
% 3.84/0.98    r1_tarski(sK2,sK1)),
% 3.84/0.98    inference(cnf_transformation,[],[f18])).
% 3.84/0.98  
% 3.84/0.98  fof(f2,axiom,(
% 3.84/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f20,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f2])).
% 3.84/0.98  
% 3.84/0.98  fof(f30,plain,(
% 3.84/0.98    r1_tarski(sK0,sK1)),
% 3.84/0.98    inference(cnf_transformation,[],[f18])).
% 3.84/0.98  
% 3.84/0.98  fof(f8,axiom,(
% 3.84/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f27,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.84/0.98    inference(cnf_transformation,[],[f8])).
% 3.84/0.98  
% 3.84/0.98  fof(f4,axiom,(
% 3.84/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f23,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.84/0.98    inference(cnf_transformation,[],[f4])).
% 3.84/0.98  
% 3.84/0.98  fof(f34,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.84/0.98    inference(definition_unfolding,[],[f27,f23,f23])).
% 3.84/0.98  
% 3.84/0.98  fof(f7,axiom,(
% 3.84/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f26,plain,(
% 3.84/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.84/0.98    inference(cnf_transformation,[],[f7])).
% 3.84/0.98  
% 3.84/0.98  fof(f38,plain,(
% 3.84/0.98    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.84/0.98    inference(definition_unfolding,[],[f26,f23])).
% 3.84/0.98  
% 3.84/0.98  fof(f6,axiom,(
% 3.84/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f25,plain,(
% 3.84/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f6])).
% 3.84/0.98  
% 3.84/0.98  fof(f10,axiom,(
% 3.84/0.98    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f29,plain,(
% 3.84/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f10])).
% 3.84/0.98  
% 3.84/0.98  fof(f9,axiom,(
% 3.84/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f28,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.84/0.98    inference(cnf_transformation,[],[f9])).
% 3.84/0.98  
% 3.84/0.98  fof(f33,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.84/0.98    inference(definition_unfolding,[],[f28,f23])).
% 3.84/0.98  
% 3.84/0.98  fof(f39,plain,(
% 3.84/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))) )),
% 3.84/0.98    inference(definition_unfolding,[],[f29,f33,f23,f33,f23,f33,f23])).
% 3.84/0.98  
% 3.84/0.98  fof(f1,axiom,(
% 3.84/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f19,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f1])).
% 3.84/0.98  
% 3.84/0.98  fof(f35,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.84/0.98    inference(definition_unfolding,[],[f19,f33,f33])).
% 3.84/0.98  
% 3.84/0.98  fof(f3,axiom,(
% 3.84/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.98  
% 3.84/0.98  fof(f16,plain,(
% 3.84/0.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.84/0.98    inference(nnf_transformation,[],[f3])).
% 3.84/0.98  
% 3.84/0.98  fof(f22,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.84/0.98    inference(cnf_transformation,[],[f16])).
% 3.84/0.98  
% 3.84/0.98  fof(f36,plain,(
% 3.84/0.98    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.84/0.98    inference(definition_unfolding,[],[f22,f23])).
% 3.84/0.98  
% 3.84/0.98  fof(f21,plain,(
% 3.84/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.84/0.98    inference(cnf_transformation,[],[f16])).
% 3.84/0.98  
% 3.84/0.98  fof(f37,plain,(
% 3.84/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.84/0.98    inference(definition_unfolding,[],[f21,f23])).
% 3.84/0.98  
% 3.84/0.98  fof(f32,plain,(
% 3.84/0.98    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 3.84/0.98    inference(cnf_transformation,[],[f18])).
% 3.84/0.98  
% 3.84/0.98  cnf(c_5,plain,
% 3.84/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.84/0.98      inference(cnf_transformation,[],[f24]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_10,negated_conjecture,
% 3.84/0.98      ( r1_tarski(sK2,sK1) ),
% 3.84/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_131,plain,
% 3.84/0.98      ( k3_xboole_0(X0,X1) = X0 | sK1 != X1 | sK2 != X0 ),
% 3.84/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_132,plain,
% 3.84/0.98      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 3.84/0.98      inference(unflattening,[status(thm)],[c_131]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2,plain,
% 3.84/0.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.84/0.98      inference(cnf_transformation,[],[f20]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_11,negated_conjecture,
% 3.84/0.98      ( r1_tarski(sK0,sK1) ),
% 3.84/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_141,plain,
% 3.84/0.98      ( k3_xboole_0(X0,X1) = X0 | sK1 != X1 | sK0 != X0 ),
% 3.84/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_142,plain,
% 3.84/0.98      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 3.84/0.98      inference(unflattening,[status(thm)],[c_141]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_0,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.84/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_346,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1409,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,sK0) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_142,c_346]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1541,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_1409,c_0]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1863,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_1541]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1874,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_1863,c_142]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_341,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1873,plain,
% 3.84/0.98      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_1541,c_341]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1875,plain,
% 3.84/0.98      ( k3_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_1874,c_1873]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1867,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)))) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_1541,c_0]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1876,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_1875,c_1867]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1877,plain,
% 3.84/0.98      ( k3_xboole_0(sK1,k3_xboole_0(sK1,sK0)) = k3_xboole_0(sK1,sK0) ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_1876,c_1409]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2227,plain,
% 3.84/0.98      ( k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(k3_xboole_0(sK1,sK0),k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0)))) = k3_xboole_0(k3_xboole_0(sK1,sK0),sK1) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_1877,c_346]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_7,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.84/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_390,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_834,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,X0) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_390,c_0]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_913,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X0))) = k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_834,c_0]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_908,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(X0,X0) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_834]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_6,plain,
% 3.84/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.84/0.98      inference(cnf_transformation,[],[f25]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_115,plain,
% 3.84/0.98      ( X0 != X1 | k3_xboole_0(X2,X1) = X2 | k1_xboole_0 != X2 ),
% 3.84/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_6]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_116,plain,
% 3.84/0.98      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.84/0.98      inference(unflattening,[status(thm)],[c_115]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_922,plain,
% 3.84/0.98      ( k3_xboole_0(X0,X0) = X0 ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_908,c_7,c_116]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_983,plain,
% 3.84/0.98      ( k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,X0) ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_913,c_922]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1311,plain,
% 3.84/0.98      ( k5_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_922,c_390]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2240,plain,
% 3.84/0.98      ( k5_xboole_0(k3_xboole_0(sK1,sK0),k5_xboole_0(k3_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK0))) = k3_xboole_0(k3_xboole_0(sK1,sK0),sK1) ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_2227,c_983,c_1311]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2241,plain,
% 3.84/0.98      ( k3_xboole_0(k3_xboole_0(sK1,sK0),sK1) = k3_xboole_0(sK1,sK0) ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_2240,c_7,c_1311]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2467,plain,
% 3.84/0.98      ( k3_xboole_0(k3_xboole_0(sK0,sK1),sK1) = k3_xboole_0(sK1,sK0) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_2241]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2493,plain,
% 3.84/0.98      ( k3_xboole_0(sK1,sK0) = sK0 ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_2467,c_142]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_8,plain,
% 3.84/0.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 3.84/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_485,plain,
% 3.84/0.98      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_8]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_4172,plain,
% 3.84/0.98      ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))))))) = k5_xboole_0(k5_xboole_0(sK0,X0),k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2493,c_485]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.84/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_404,plain,
% 3.84/0.98      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_142,c_1]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_3,plain,
% 3.84/0.98      ( ~ r1_tarski(X0,X1)
% 3.84/0.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.84/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_61,plain,
% 3.84/0.98      ( ~ r1_tarski(X0,X1)
% 3.84/0.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.84/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_146,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.84/0.98      | sK1 != X1
% 3.84/0.98      | sK0 != X0 ),
% 3.84/0.98      inference(resolution_lifted,[status(thm)],[c_61,c_11]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_147,plain,
% 3.84/0.98      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 3.84/0.98      inference(unflattening,[status(thm)],[c_146]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_192,plain,
% 3.84/0.98      ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_147,c_142]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_405,plain,
% 3.84/0.98      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_404,c_192]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_388,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_7]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_391,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_388,c_116]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_406,plain,
% 3.84/0.98      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = sK1 ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_405,c_391]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_594,plain,
% 3.84/0.98      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = sK1 ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_406]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_600,plain,
% 3.84/0.98      ( k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)) = sK1 ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_594,c_142]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_4207,plain,
% 3.84/0.98      ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,sK1))))) = k5_xboole_0(k5_xboole_0(sK0,X0),k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_4172,c_600]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_4764,plain,
% 3.84/0.98      ( k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k5_xboole_0(sK2,sK2)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_132,c_4207]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_136,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.84/0.98      | sK1 != X1
% 3.84/0.98      | sK2 != X0 ),
% 3.84/0.98      inference(resolution_lifted,[status(thm)],[c_61,c_10]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_137,plain,
% 3.84/0.98      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 3.84/0.98      inference(unflattening,[status(thm)],[c_136]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_193,plain,
% 3.84/0.98      ( k5_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_137,c_132]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_403,plain,
% 3.84/0.98      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_132,c_1]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_407,plain,
% 3.84/0.98      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_403,c_193]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_408,plain,
% 3.84/0.98      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK1 ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_407,c_391]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_670,plain,
% 3.84/0.98      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK1 ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_408]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_676,plain,
% 3.84/0.98      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_670,c_132]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1408,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,sK2) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_132,c_346]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1491,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_1408,c_0]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1640,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_1491]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1650,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_1640,c_132]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1654,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_1650]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1664,plain,
% 3.84/0.98      ( k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_1654,c_132]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1749,plain,
% 3.84/0.98      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_1664,c_341]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1719,plain,
% 3.84/0.98      ( k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_1664,c_1408]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_1763,plain,
% 3.84/0.98      ( k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_1749,c_1664,c_1719]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2189,plain,
% 3.84/0.98      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK1) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_1763,c_346]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2202,plain,
% 3.84/0.98      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK1) ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_2189,c_983,c_1311]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2203,plain,
% 3.84/0.98      ( k3_xboole_0(k3_xboole_0(sK1,sK2),sK1) = k3_xboole_0(sK1,sK2) ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_2202,c_7,c_1311]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2407,plain,
% 3.84/0.98      ( k3_xboole_0(k3_xboole_0(sK2,sK1),sK1) = k3_xboole_0(sK1,sK2) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_2,c_2203]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_2431,plain,
% 3.84/0.98      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_2407,c_132]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_4786,plain,
% 3.84/0.98      ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 3.84/0.98      inference(light_normalisation,
% 3.84/0.98                [status(thm)],
% 3.84/0.98                [c_4764,c_142,c_192,c_193,c_676,c_2431]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_400,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.84/0.98      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_121,plain,
% 3.84/0.98      ( X0 != X1
% 3.84/0.98      | k5_xboole_0(X2,k3_xboole_0(X2,X1)) = k1_xboole_0
% 3.84/0.98      | k1_xboole_0 != X2 ),
% 3.84/0.98      inference(resolution_lifted,[status(thm)],[c_61,c_6]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_122,plain,
% 3.84/0.98      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.84/0.98      inference(unflattening,[status(thm)],[c_121]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_194,plain,
% 3.84/0.98      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.84/0.98      inference(light_normalisation,[status(thm)],[c_122,c_116]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_409,plain,
% 3.84/0.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.84/0.98      inference(light_normalisation,
% 3.84/0.98                [status(thm)],
% 3.84/0.98                [c_400,c_116,c_194,c_391]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_4787,plain,
% 3.84/0.98      ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k1_xboole_0 ),
% 3.84/0.98      inference(demodulation,[status(thm)],[c_4786,c_116,c_409]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_4,plain,
% 3.84/0.98      ( r1_tarski(X0,X1)
% 3.84/0.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.84/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_59,plain,
% 3.84/0.98      ( r1_tarski(X0,X1)
% 3.84/0.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.84/0.98      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_9,negated_conjecture,
% 3.84/0.98      ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
% 3.84/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_126,plain,
% 3.84/0.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 3.84/0.98      | k5_xboole_0(sK0,sK2) != X0
% 3.84/0.98      | sK1 != X1 ),
% 3.84/0.98      inference(resolution_lifted,[status(thm)],[c_59,c_9]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(c_127,plain,
% 3.84/0.98      ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) != k1_xboole_0 ),
% 3.84/0.98      inference(unflattening,[status(thm)],[c_126]) ).
% 3.84/0.98  
% 3.84/0.98  cnf(contradiction,plain,
% 3.84/0.98      ( $false ),
% 3.84/0.98      inference(minisat,[status(thm)],[c_4787,c_127]) ).
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/0.98  
% 3.84/0.98  ------                               Statistics
% 3.84/0.98  
% 3.84/0.98  ------ General
% 3.84/0.98  
% 3.84/0.98  abstr_ref_over_cycles:                  0
% 3.84/0.98  abstr_ref_under_cycles:                 0
% 3.84/0.98  gc_basic_clause_elim:                   0
% 3.84/0.98  forced_gc_time:                         0
% 3.84/0.98  parsing_time:                           0.009
% 3.84/0.98  unif_index_cands_time:                  0.
% 3.84/0.98  unif_index_add_time:                    0.
% 3.84/0.98  orderings_time:                         0.
% 3.84/0.98  out_proof_time:                         0.009
% 3.84/0.98  total_time:                             0.325
% 3.84/0.98  num_of_symbols:                         38
% 3.84/0.98  num_of_terms:                           8692
% 3.84/0.98  
% 3.84/0.98  ------ Preprocessing
% 3.84/0.98  
% 3.84/0.98  num_of_splits:                          0
% 3.84/0.98  num_of_split_atoms:                     0
% 3.84/0.98  num_of_reused_defs:                     0
% 3.84/0.98  num_eq_ax_congr_red:                    0
% 3.84/0.98  num_of_sem_filtered_clauses:            0
% 3.84/0.98  num_of_subtypes:                        0
% 3.84/0.98  monotx_restored_types:                  0
% 3.84/0.98  sat_num_of_epr_types:                   0
% 3.84/0.98  sat_num_of_non_cyclic_types:            0
% 3.84/0.98  sat_guarded_non_collapsed_types:        0
% 3.84/0.98  num_pure_diseq_elim:                    0
% 3.84/0.98  simp_replaced_by:                       0
% 3.84/0.98  res_preprocessed:                       32
% 3.84/0.98  prep_upred:                             0
% 3.84/0.98  prep_unflattend:                        15
% 3.84/0.98  smt_new_axioms:                         0
% 3.84/0.98  pred_elim_cands:                        1
% 3.84/0.98  pred_elim:                              1
% 3.84/0.98  pred_elim_cl:                           -4
% 3.84/0.98  pred_elim_cycles:                       2
% 3.84/0.98  merged_defs:                            2
% 3.84/0.98  merged_defs_ncl:                        0
% 3.84/0.98  bin_hyper_res:                          2
% 3.84/0.98  prep_cycles:                            2
% 3.84/0.98  pred_elim_time:                         0.002
% 3.84/0.98  splitting_time:                         0.
% 3.84/0.98  sem_filter_time:                        0.
% 3.84/0.98  monotx_time:                            0.001
% 3.84/0.98  subtype_inf_time:                       0.
% 3.84/0.98  
% 3.84/0.98  ------ Problem properties
% 3.84/0.98  
% 3.84/0.98  clauses:                                16
% 3.84/0.98  conjectures:                            0
% 3.84/0.98  epr:                                    0
% 3.84/0.98  horn:                                   16
% 3.84/0.98  ground:                                 8
% 3.84/0.98  unary:                                  13
% 3.84/0.98  binary:                                 3
% 3.84/0.98  lits:                                   19
% 3.84/0.98  lits_eq:                                19
% 3.84/0.98  fd_pure:                                0
% 3.84/0.98  fd_pseudo:                              0
% 3.84/0.98  fd_cond:                                0
% 3.84/0.98  fd_pseudo_cond:                         0
% 3.84/0.98  ac_symbols:                             0
% 3.84/0.98  
% 3.84/0.98  ------ Propositional Solver
% 3.84/0.98  
% 3.84/0.98  prop_solver_calls:                      24
% 3.84/0.98  prop_fast_solver_calls:                 222
% 3.84/0.98  smt_solver_calls:                       0
% 3.84/0.98  smt_fast_solver_calls:                  0
% 3.84/0.98  prop_num_of_clauses:                    1754
% 3.84/0.98  prop_preprocess_simplified:             2911
% 3.84/0.98  prop_fo_subsumed:                       0
% 3.84/0.98  prop_solver_time:                       0.
% 3.84/0.98  smt_solver_time:                        0.
% 3.84/0.98  smt_fast_solver_time:                   0.
% 3.84/0.98  prop_fast_solver_time:                  0.
% 3.84/0.98  prop_unsat_core_time:                   0.
% 3.84/0.98  
% 3.84/0.98  ------ QBF
% 3.84/0.98  
% 3.84/0.98  qbf_q_res:                              0
% 3.84/0.98  qbf_num_tautologies:                    0
% 3.84/0.98  qbf_prep_cycles:                        0
% 3.84/0.98  
% 3.84/0.98  ------ BMC1
% 3.84/0.98  
% 3.84/0.98  bmc1_current_bound:                     -1
% 3.84/0.98  bmc1_last_solved_bound:                 -1
% 3.84/0.98  bmc1_unsat_core_size:                   -1
% 3.84/0.98  bmc1_unsat_core_parents_size:           -1
% 3.84/0.98  bmc1_merge_next_fun:                    0
% 3.84/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.84/0.98  
% 3.84/0.98  ------ Instantiation
% 3.84/0.98  
% 3.84/0.98  inst_num_of_clauses:                    886
% 3.84/0.98  inst_num_in_passive:                    299
% 3.84/0.98  inst_num_in_active:                     405
% 3.84/0.98  inst_num_in_unprocessed:                182
% 3.84/0.98  inst_num_of_loops:                      460
% 3.84/0.98  inst_num_of_learning_restarts:          0
% 3.84/0.98  inst_num_moves_active_passive:          49
% 3.84/0.98  inst_lit_activity:                      0
% 3.84/0.98  inst_lit_activity_moves:                0
% 3.84/0.98  inst_num_tautologies:                   0
% 3.84/0.98  inst_num_prop_implied:                  0
% 3.84/0.98  inst_num_existing_simplified:           0
% 3.84/0.98  inst_num_eq_res_simplified:             0
% 3.84/0.98  inst_num_child_elim:                    0
% 3.84/0.98  inst_num_of_dismatching_blockings:      335
% 3.84/0.98  inst_num_of_non_proper_insts:           1091
% 3.84/0.98  inst_num_of_duplicates:                 0
% 3.84/0.98  inst_inst_num_from_inst_to_res:         0
% 3.84/0.98  inst_dismatching_checking_time:         0.
% 3.84/0.98  
% 3.84/0.98  ------ Resolution
% 3.84/0.98  
% 3.84/0.98  res_num_of_clauses:                     0
% 3.84/0.98  res_num_in_passive:                     0
% 3.84/0.98  res_num_in_active:                      0
% 3.84/0.98  res_num_of_loops:                       34
% 3.84/0.98  res_forward_subset_subsumed:            204
% 3.84/0.98  res_backward_subset_subsumed:           0
% 3.84/0.98  res_forward_subsumed:                   0
% 3.84/0.98  res_backward_subsumed:                  0
% 3.84/0.98  res_forward_subsumption_resolution:     0
% 3.84/0.98  res_backward_subsumption_resolution:    0
% 3.84/0.98  res_clause_to_clause_subsumption:       2509
% 3.84/0.98  res_orphan_elimination:                 0
% 3.84/0.98  res_tautology_del:                      75
% 3.84/0.98  res_num_eq_res_simplified:              2
% 3.84/0.98  res_num_sel_changes:                    0
% 3.84/0.98  res_moves_from_active_to_pass:          0
% 3.84/0.98  
% 3.84/0.98  ------ Superposition
% 3.84/0.98  
% 3.84/0.98  sup_time_total:                         0.
% 3.84/0.98  sup_time_generating:                    0.
% 3.84/0.98  sup_time_sim_full:                      0.
% 3.84/0.98  sup_time_sim_immed:                     0.
% 3.84/0.98  
% 3.84/0.98  sup_num_of_clauses:                     328
% 3.84/0.98  sup_num_in_active:                      61
% 3.84/0.98  sup_num_in_passive:                     267
% 3.84/0.98  sup_num_of_loops:                       90
% 3.84/0.98  sup_fw_superposition:                   651
% 3.84/0.98  sup_bw_superposition:                   631
% 3.84/0.98  sup_immediate_simplified:               492
% 3.84/0.98  sup_given_eliminated:                   7
% 3.84/0.98  comparisons_done:                       0
% 3.84/0.98  comparisons_avoided:                    0
% 3.84/0.98  
% 3.84/0.98  ------ Simplifications
% 3.84/0.98  
% 3.84/0.98  
% 3.84/0.98  sim_fw_subset_subsumed:                 12
% 3.84/0.98  sim_bw_subset_subsumed:                 1
% 3.84/0.98  sim_fw_subsumed:                        12
% 3.84/0.98  sim_bw_subsumed:                        14
% 3.84/0.98  sim_fw_subsumption_res:                 0
% 3.84/0.98  sim_bw_subsumption_res:                 0
% 3.84/0.98  sim_tautology_del:                      6
% 3.84/0.98  sim_eq_tautology_del:                   165
% 3.84/0.98  sim_eq_res_simp:                        2
% 3.84/0.98  sim_fw_demodulated:                     354
% 3.84/0.98  sim_bw_demodulated:                     72
% 3.84/0.98  sim_light_normalised:                   320
% 3.84/0.98  sim_joinable_taut:                      0
% 3.84/0.98  sim_joinable_simp:                      0
% 3.84/0.98  sim_ac_normalised:                      0
% 3.84/0.98  sim_smt_subsumption:                    0
% 3.84/0.98  
%------------------------------------------------------------------------------
