%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:06 EST 2020

% Result     : Theorem 15.31s
% Output     : CNFRefutation 15.31s
% Verified   : 
% Statistics : Number of formulae       :  162 (6275 expanded)
%              Number of clauses        :  121 (2409 expanded)
%              Number of leaves         :   15 (1674 expanded)
%              Depth                    :   32
%              Number of atoms          :  190 (7938 expanded)
%              Number of equality atoms :  151 (5862 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   11 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f36,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f34,f23])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) ),
    inference(definition_unfolding,[],[f35,f23,f39,f23,f39,f23,f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f28,f23,f23])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f29,f39,f23])).

fof(f37,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_326,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_9])).

cnf(c_1599,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10,c_326])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1637,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1599,c_7])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_101,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_102,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_143,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X2))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X2)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X2,k5_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_11,c_1,c_0])).

cnf(c_1420,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))))))) = k5_xboole_0(k5_xboole_0(X0,sK0),k3_xboole_0(sK1,k5_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_102,c_143])).

cnf(c_2098,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1)))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK0),k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK0))) ),
    inference(superposition,[status(thm)],[c_1637,c_1420])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_84,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_85,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_84])).

cnf(c_142,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_85,c_1,c_0])).

cnf(c_389,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_142,c_0])).

cnf(c_1440,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))))),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))))),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_389,c_143])).

cnf(c_1454,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_389,c_143])).

cnf(c_1483,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X0))) ),
    inference(demodulation,[status(thm)],[c_1454,c_7,c_389])).

cnf(c_1497,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))))),k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))))))))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_1440,c_1483])).

cnf(c_1498,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))))),k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))))))))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1497,c_7])).

cnf(c_325,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_9])).

cnf(c_1499,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))),k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))))))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_1498,c_7,c_325,c_389])).

cnf(c_1500,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_1499,c_7,c_389])).

cnf(c_1501,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_1500,c_1483])).

cnf(c_2120,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_2098,c_7,c_10,c_102,c_142,c_389,c_1501,c_1637])).

cnf(c_2121,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2120,c_389])).

cnf(c_8,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_90,plain,
    ( X0 != X1
    | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) != X3
    | k3_xboole_0(X1,X3) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_91,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(unflattening,[status(thm)],[c_90])).

cnf(c_141,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_91,c_1,c_0])).

cnf(c_692,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_142,c_141])).

cnf(c_706,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_692,c_325])).

cnf(c_707,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_706,c_7])).

cnf(c_786,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_707,c_1])).

cnf(c_1809,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_786])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_145,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_1,c_0])).

cnf(c_4273,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1809,c_145])).

cnf(c_4377,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4273,c_10])).

cnf(c_6,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_144,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_6,c_1,c_0])).

cnf(c_4495,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(demodulation,[status(thm)],[c_4377,c_144])).

cnf(c_4496,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4495,c_142])).

cnf(c_4497,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_4496,c_7])).

cnf(c_7256,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_4497])).

cnf(c_15247,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)) = sK1 ),
    inference(superposition,[status(thm)],[c_102,c_7256])).

cnf(c_15863,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,sK0),X0)) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_15247,c_9])).

cnf(c_20078,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,X0))) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_9,c_15863])).

cnf(c_27172,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2121,c_20078])).

cnf(c_162,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_3138,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_102,c_162])).

cnf(c_3685,plain,
    ( k3_xboole_0(sK0,sK0) = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_707,c_3138])).

cnf(c_3722,plain,
    ( k3_xboole_0(sK1,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_3685,c_707])).

cnf(c_27193,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_27172,c_3722])).

cnf(c_27194,plain,
    ( k5_xboole_0(sK0,sK1) = k5_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_27193,c_7])).

cnf(c_27230,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_27194,c_9])).

cnf(c_37780,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_27230,c_9])).

cnf(c_4272,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_707,c_145])).

cnf(c_2860,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_786,c_1809])).

cnf(c_2896,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2860,c_707])).

cnf(c_4378,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_4272,c_2896])).

cnf(c_4379,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4378,c_10])).

cnf(c_6974,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_4379])).

cnf(c_13553,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),k1_xboole_0))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6974,c_141])).

cnf(c_13588,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_13553,c_7,c_7256])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_96,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_97,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(unflattening,[status(thm)],[c_96])).

cnf(c_1419,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))))))) = k5_xboole_0(k5_xboole_0(X0,sK2),k3_xboole_0(sK1,k5_xboole_0(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_97,c_143])).

cnf(c_13828,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK1,k3_xboole_0(X0,sK1))))),k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))))))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK1),sK2),k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(X0,sK1),sK2))) ),
    inference(superposition,[status(thm)],[c_13588,c_1419])).

cnf(c_13901,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK1),sK2),k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(X0,sK1),sK2))) = k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_13828,c_7,c_10,c_97,c_142,c_1637,c_7256])).

cnf(c_14039,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_102,c_13901])).

cnf(c_14075,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) ),
    inference(light_normalisation,[status(thm)],[c_14039,c_102])).

cnf(c_15228,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) = k5_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_14075,c_7256])).

cnf(c_15246,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_97,c_7256])).

cnf(c_15375,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_15228,c_15246])).

cnf(c_15376,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)),k5_xboole_0(sK0,sK0)) = k5_xboole_0(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_15375,c_102])).

cnf(c_15377,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) = k5_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_15376,c_7,c_10])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_111,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != sK1
    | k5_xboole_0(sK0,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_112,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2)))) != sK1 ),
    inference(unflattening,[status(thm)],[c_111])).

cnf(c_321,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_9,c_112])).

cnf(c_15436,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK0,sK2)))) != sK1 ),
    inference(superposition,[status(thm)],[c_15377,c_321])).

cnf(c_44915,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_37780,c_15436])).

cnf(c_1912,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1)))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK2))) ),
    inference(superposition,[status(thm)],[c_1637,c_1419])).

cnf(c_1934,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_1912,c_7,c_10,c_97,c_142,c_389,c_1501,c_1637])).

cnf(c_1935,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1934,c_389])).

cnf(c_15776,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_15246,c_9])).

cnf(c_19991,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0))) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_9,c_15776])).

cnf(c_25514,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1935,c_19991])).

cnf(c_3137,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_97,c_162])).

cnf(c_3589,plain,
    ( k3_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_707,c_3137])).

cnf(c_3626,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_3589,c_707])).

cnf(c_25534,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_25514,c_3626])).

cnf(c_25535,plain,
    ( k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_25534,c_7])).

cnf(c_27217,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_27194,c_15247])).

cnf(c_25562,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_25535,c_9])).

cnf(c_35873,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_25562,c_9])).

cnf(c_328,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_10])).

cnf(c_27170,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_328,c_20078])).

cnf(c_27198,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK0,X0))) = k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_27170,c_7])).

cnf(c_43317,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_35873,c_27198])).

cnf(c_25512,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK2,X0))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_328,c_19991])).

cnf(c_25539,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK2,X0))) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_25512,c_7])).

cnf(c_35819,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_25539,c_20078])).

cnf(c_20080,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,sK0),X0))) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_328,c_15863])).

cnf(c_20107,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,sK0),X0))) = sK0 ),
    inference(demodulation,[status(thm)],[c_20080,c_7])).

cnf(c_28511,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(sK0,X0)))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_20107,c_20107,c_27194,c_27230])).

cnf(c_28536,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_28511,c_19991])).

cnf(c_1638,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1637,c_326])).

cnf(c_28541,plain,
    ( k5_xboole_0(sK2,sK0) = k5_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_28536,c_1638])).

cnf(c_35821,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_35819,c_28541])).

cnf(c_43320,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_43317,c_35821])).

cnf(c_44918,plain,
    ( sK1 != sK1 ),
    inference(light_normalisation,[status(thm)],[c_44915,c_25535,c_27217,c_43320])).

cnf(c_44919,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_44918])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:01:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.31/2.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.31/2.47  
% 15.31/2.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.31/2.47  
% 15.31/2.47  ------  iProver source info
% 15.31/2.47  
% 15.31/2.47  git: date: 2020-06-30 10:37:57 +0100
% 15.31/2.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.31/2.47  git: non_committed_changes: false
% 15.31/2.47  git: last_make_outside_of_git: false
% 15.31/2.47  
% 15.31/2.47  ------ 
% 15.31/2.47  
% 15.31/2.47  ------ Input Options
% 15.31/2.47  
% 15.31/2.47  --out_options                           all
% 15.31/2.47  --tptp_safe_out                         true
% 15.31/2.47  --problem_path                          ""
% 15.31/2.47  --include_path                          ""
% 15.31/2.47  --clausifier                            res/vclausify_rel
% 15.31/2.47  --clausifier_options                    ""
% 15.31/2.47  --stdin                                 false
% 15.31/2.47  --stats_out                             all
% 15.31/2.47  
% 15.31/2.47  ------ General Options
% 15.31/2.47  
% 15.31/2.47  --fof                                   false
% 15.31/2.47  --time_out_real                         305.
% 15.31/2.47  --time_out_virtual                      -1.
% 15.31/2.47  --symbol_type_check                     false
% 15.31/2.47  --clausify_out                          false
% 15.31/2.47  --sig_cnt_out                           false
% 15.31/2.47  --trig_cnt_out                          false
% 15.31/2.47  --trig_cnt_out_tolerance                1.
% 15.31/2.47  --trig_cnt_out_sk_spl                   false
% 15.31/2.47  --abstr_cl_out                          false
% 15.31/2.47  
% 15.31/2.47  ------ Global Options
% 15.31/2.47  
% 15.31/2.47  --schedule                              default
% 15.31/2.47  --add_important_lit                     false
% 15.31/2.47  --prop_solver_per_cl                    1000
% 15.31/2.47  --min_unsat_core                        false
% 15.31/2.47  --soft_assumptions                      false
% 15.31/2.47  --soft_lemma_size                       3
% 15.31/2.47  --prop_impl_unit_size                   0
% 15.31/2.47  --prop_impl_unit                        []
% 15.31/2.47  --share_sel_clauses                     true
% 15.31/2.47  --reset_solvers                         false
% 15.31/2.47  --bc_imp_inh                            [conj_cone]
% 15.31/2.47  --conj_cone_tolerance                   3.
% 15.31/2.47  --extra_neg_conj                        none
% 15.31/2.47  --large_theory_mode                     true
% 15.31/2.47  --prolific_symb_bound                   200
% 15.31/2.47  --lt_threshold                          2000
% 15.31/2.47  --clause_weak_htbl                      true
% 15.31/2.47  --gc_record_bc_elim                     false
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing Options
% 15.31/2.47  
% 15.31/2.47  --preprocessing_flag                    true
% 15.31/2.47  --time_out_prep_mult                    0.1
% 15.31/2.47  --splitting_mode                        input
% 15.31/2.47  --splitting_grd                         true
% 15.31/2.47  --splitting_cvd                         false
% 15.31/2.47  --splitting_cvd_svl                     false
% 15.31/2.47  --splitting_nvd                         32
% 15.31/2.47  --sub_typing                            true
% 15.31/2.47  --prep_gs_sim                           true
% 15.31/2.47  --prep_unflatten                        true
% 15.31/2.47  --prep_res_sim                          true
% 15.31/2.47  --prep_upred                            true
% 15.31/2.47  --prep_sem_filter                       exhaustive
% 15.31/2.47  --prep_sem_filter_out                   false
% 15.31/2.47  --pred_elim                             true
% 15.31/2.47  --res_sim_input                         true
% 15.31/2.47  --eq_ax_congr_red                       true
% 15.31/2.47  --pure_diseq_elim                       true
% 15.31/2.47  --brand_transform                       false
% 15.31/2.47  --non_eq_to_eq                          false
% 15.31/2.47  --prep_def_merge                        true
% 15.31/2.47  --prep_def_merge_prop_impl              false
% 15.31/2.47  --prep_def_merge_mbd                    true
% 15.31/2.47  --prep_def_merge_tr_red                 false
% 15.31/2.47  --prep_def_merge_tr_cl                  false
% 15.31/2.47  --smt_preprocessing                     true
% 15.31/2.47  --smt_ac_axioms                         fast
% 15.31/2.47  --preprocessed_out                      false
% 15.31/2.47  --preprocessed_stats                    false
% 15.31/2.47  
% 15.31/2.47  ------ Abstraction refinement Options
% 15.31/2.47  
% 15.31/2.47  --abstr_ref                             []
% 15.31/2.47  --abstr_ref_prep                        false
% 15.31/2.47  --abstr_ref_until_sat                   false
% 15.31/2.47  --abstr_ref_sig_restrict                funpre
% 15.31/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 15.31/2.47  --abstr_ref_under                       []
% 15.31/2.47  
% 15.31/2.47  ------ SAT Options
% 15.31/2.47  
% 15.31/2.47  --sat_mode                              false
% 15.31/2.47  --sat_fm_restart_options                ""
% 15.31/2.47  --sat_gr_def                            false
% 15.31/2.47  --sat_epr_types                         true
% 15.31/2.47  --sat_non_cyclic_types                  false
% 15.31/2.47  --sat_finite_models                     false
% 15.31/2.47  --sat_fm_lemmas                         false
% 15.31/2.47  --sat_fm_prep                           false
% 15.31/2.47  --sat_fm_uc_incr                        true
% 15.31/2.47  --sat_out_model                         small
% 15.31/2.47  --sat_out_clauses                       false
% 15.31/2.47  
% 15.31/2.47  ------ QBF Options
% 15.31/2.47  
% 15.31/2.47  --qbf_mode                              false
% 15.31/2.47  --qbf_elim_univ                         false
% 15.31/2.47  --qbf_dom_inst                          none
% 15.31/2.47  --qbf_dom_pre_inst                      false
% 15.31/2.47  --qbf_sk_in                             false
% 15.31/2.47  --qbf_pred_elim                         true
% 15.31/2.47  --qbf_split                             512
% 15.31/2.47  
% 15.31/2.47  ------ BMC1 Options
% 15.31/2.47  
% 15.31/2.47  --bmc1_incremental                      false
% 15.31/2.47  --bmc1_axioms                           reachable_all
% 15.31/2.47  --bmc1_min_bound                        0
% 15.31/2.47  --bmc1_max_bound                        -1
% 15.31/2.47  --bmc1_max_bound_default                -1
% 15.31/2.47  --bmc1_symbol_reachability              true
% 15.31/2.47  --bmc1_property_lemmas                  false
% 15.31/2.47  --bmc1_k_induction                      false
% 15.31/2.47  --bmc1_non_equiv_states                 false
% 15.31/2.47  --bmc1_deadlock                         false
% 15.31/2.47  --bmc1_ucm                              false
% 15.31/2.47  --bmc1_add_unsat_core                   none
% 15.31/2.47  --bmc1_unsat_core_children              false
% 15.31/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 15.31/2.47  --bmc1_out_stat                         full
% 15.31/2.47  --bmc1_ground_init                      false
% 15.31/2.47  --bmc1_pre_inst_next_state              false
% 15.31/2.47  --bmc1_pre_inst_state                   false
% 15.31/2.47  --bmc1_pre_inst_reach_state             false
% 15.31/2.47  --bmc1_out_unsat_core                   false
% 15.31/2.47  --bmc1_aig_witness_out                  false
% 15.31/2.47  --bmc1_verbose                          false
% 15.31/2.47  --bmc1_dump_clauses_tptp                false
% 15.31/2.47  --bmc1_dump_unsat_core_tptp             false
% 15.31/2.47  --bmc1_dump_file                        -
% 15.31/2.47  --bmc1_ucm_expand_uc_limit              128
% 15.31/2.47  --bmc1_ucm_n_expand_iterations          6
% 15.31/2.47  --bmc1_ucm_extend_mode                  1
% 15.31/2.47  --bmc1_ucm_init_mode                    2
% 15.31/2.47  --bmc1_ucm_cone_mode                    none
% 15.31/2.47  --bmc1_ucm_reduced_relation_type        0
% 15.31/2.47  --bmc1_ucm_relax_model                  4
% 15.31/2.47  --bmc1_ucm_full_tr_after_sat            true
% 15.31/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 15.31/2.47  --bmc1_ucm_layered_model                none
% 15.31/2.47  --bmc1_ucm_max_lemma_size               10
% 15.31/2.47  
% 15.31/2.47  ------ AIG Options
% 15.31/2.47  
% 15.31/2.47  --aig_mode                              false
% 15.31/2.47  
% 15.31/2.47  ------ Instantiation Options
% 15.31/2.47  
% 15.31/2.47  --instantiation_flag                    true
% 15.31/2.47  --inst_sos_flag                         true
% 15.31/2.47  --inst_sos_phase                        true
% 15.31/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.31/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.31/2.47  --inst_lit_sel_side                     num_symb
% 15.31/2.47  --inst_solver_per_active                1400
% 15.31/2.47  --inst_solver_calls_frac                1.
% 15.31/2.47  --inst_passive_queue_type               priority_queues
% 15.31/2.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.31/2.47  --inst_passive_queues_freq              [25;2]
% 15.31/2.47  --inst_dismatching                      true
% 15.31/2.47  --inst_eager_unprocessed_to_passive     true
% 15.31/2.47  --inst_prop_sim_given                   true
% 15.31/2.47  --inst_prop_sim_new                     false
% 15.31/2.47  --inst_subs_new                         false
% 15.31/2.47  --inst_eq_res_simp                      false
% 15.31/2.47  --inst_subs_given                       false
% 15.31/2.47  --inst_orphan_elimination               true
% 15.31/2.47  --inst_learning_loop_flag               true
% 15.31/2.47  --inst_learning_start                   3000
% 15.31/2.47  --inst_learning_factor                  2
% 15.31/2.47  --inst_start_prop_sim_after_learn       3
% 15.31/2.47  --inst_sel_renew                        solver
% 15.31/2.47  --inst_lit_activity_flag                true
% 15.31/2.47  --inst_restr_to_given                   false
% 15.31/2.47  --inst_activity_threshold               500
% 15.31/2.47  --inst_out_proof                        true
% 15.31/2.47  
% 15.31/2.47  ------ Resolution Options
% 15.31/2.47  
% 15.31/2.47  --resolution_flag                       true
% 15.31/2.47  --res_lit_sel                           adaptive
% 15.31/2.47  --res_lit_sel_side                      none
% 15.31/2.47  --res_ordering                          kbo
% 15.31/2.47  --res_to_prop_solver                    active
% 15.31/2.47  --res_prop_simpl_new                    false
% 15.31/2.47  --res_prop_simpl_given                  true
% 15.31/2.47  --res_passive_queue_type                priority_queues
% 15.31/2.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.31/2.47  --res_passive_queues_freq               [15;5]
% 15.31/2.47  --res_forward_subs                      full
% 15.31/2.47  --res_backward_subs                     full
% 15.31/2.47  --res_forward_subs_resolution           true
% 15.31/2.47  --res_backward_subs_resolution          true
% 15.31/2.47  --res_orphan_elimination                true
% 15.31/2.47  --res_time_limit                        2.
% 15.31/2.47  --res_out_proof                         true
% 15.31/2.47  
% 15.31/2.47  ------ Superposition Options
% 15.31/2.47  
% 15.31/2.47  --superposition_flag                    true
% 15.31/2.47  --sup_passive_queue_type                priority_queues
% 15.31/2.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.31/2.47  --sup_passive_queues_freq               [8;1;4]
% 15.31/2.47  --demod_completeness_check              fast
% 15.31/2.47  --demod_use_ground                      true
% 15.31/2.47  --sup_to_prop_solver                    passive
% 15.31/2.47  --sup_prop_simpl_new                    true
% 15.31/2.47  --sup_prop_simpl_given                  true
% 15.31/2.47  --sup_fun_splitting                     true
% 15.31/2.47  --sup_smt_interval                      50000
% 15.31/2.47  
% 15.31/2.47  ------ Superposition Simplification Setup
% 15.31/2.47  
% 15.31/2.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.31/2.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.31/2.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.31/2.47  --sup_full_triv                         [TrivRules;PropSubs]
% 15.31/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.31/2.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.31/2.47  --sup_immed_triv                        [TrivRules]
% 15.31/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.47  --sup_immed_bw_main                     []
% 15.31/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.31/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 15.31/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.47  --sup_input_bw                          []
% 15.31/2.47  
% 15.31/2.47  ------ Combination Options
% 15.31/2.47  
% 15.31/2.47  --comb_res_mult                         3
% 15.31/2.47  --comb_sup_mult                         2
% 15.31/2.47  --comb_inst_mult                        10
% 15.31/2.47  
% 15.31/2.47  ------ Debug Options
% 15.31/2.47  
% 15.31/2.47  --dbg_backtrace                         false
% 15.31/2.47  --dbg_dump_prop_clauses                 false
% 15.31/2.47  --dbg_dump_prop_clauses_file            -
% 15.31/2.47  --dbg_out_stat                          false
% 15.31/2.47  ------ Parsing...
% 15.31/2.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.31/2.47  ------ Proving...
% 15.31/2.47  ------ Problem Properties 
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  clauses                                 17
% 15.31/2.47  conjectures                             0
% 15.31/2.47  EPR                                     0
% 15.31/2.47  Horn                                    17
% 15.31/2.47  unary                                   15
% 15.31/2.47  binary                                  2
% 15.31/2.47  lits                                    19
% 15.31/2.47  lits eq                                 19
% 15.31/2.47  fd_pure                                 0
% 15.31/2.47  fd_pseudo                               0
% 15.31/2.47  fd_cond                                 0
% 15.31/2.47  fd_pseudo_cond                          0
% 15.31/2.47  AC symbols                              1
% 15.31/2.47  
% 15.31/2.47  ------ Schedule dynamic 5 is on 
% 15.31/2.47  
% 15.31/2.47  ------ no conjectures: strip conj schedule 
% 15.31/2.47  
% 15.31/2.47  ------ pure equality problem: resolution off 
% 15.31/2.47  
% 15.31/2.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  ------ 
% 15.31/2.47  Current options:
% 15.31/2.47  ------ 
% 15.31/2.47  
% 15.31/2.47  ------ Input Options
% 15.31/2.47  
% 15.31/2.47  --out_options                           all
% 15.31/2.47  --tptp_safe_out                         true
% 15.31/2.47  --problem_path                          ""
% 15.31/2.47  --include_path                          ""
% 15.31/2.47  --clausifier                            res/vclausify_rel
% 15.31/2.47  --clausifier_options                    ""
% 15.31/2.47  --stdin                                 false
% 15.31/2.47  --stats_out                             all
% 15.31/2.47  
% 15.31/2.47  ------ General Options
% 15.31/2.47  
% 15.31/2.47  --fof                                   false
% 15.31/2.47  --time_out_real                         305.
% 15.31/2.47  --time_out_virtual                      -1.
% 15.31/2.47  --symbol_type_check                     false
% 15.31/2.47  --clausify_out                          false
% 15.31/2.47  --sig_cnt_out                           false
% 15.31/2.47  --trig_cnt_out                          false
% 15.31/2.47  --trig_cnt_out_tolerance                1.
% 15.31/2.47  --trig_cnt_out_sk_spl                   false
% 15.31/2.47  --abstr_cl_out                          false
% 15.31/2.47  
% 15.31/2.47  ------ Global Options
% 15.31/2.47  
% 15.31/2.47  --schedule                              default
% 15.31/2.47  --add_important_lit                     false
% 15.31/2.47  --prop_solver_per_cl                    1000
% 15.31/2.47  --min_unsat_core                        false
% 15.31/2.47  --soft_assumptions                      false
% 15.31/2.47  --soft_lemma_size                       3
% 15.31/2.47  --prop_impl_unit_size                   0
% 15.31/2.47  --prop_impl_unit                        []
% 15.31/2.47  --share_sel_clauses                     true
% 15.31/2.47  --reset_solvers                         false
% 15.31/2.47  --bc_imp_inh                            [conj_cone]
% 15.31/2.47  --conj_cone_tolerance                   3.
% 15.31/2.47  --extra_neg_conj                        none
% 15.31/2.47  --large_theory_mode                     true
% 15.31/2.47  --prolific_symb_bound                   200
% 15.31/2.47  --lt_threshold                          2000
% 15.31/2.47  --clause_weak_htbl                      true
% 15.31/2.47  --gc_record_bc_elim                     false
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing Options
% 15.31/2.47  
% 15.31/2.47  --preprocessing_flag                    true
% 15.31/2.47  --time_out_prep_mult                    0.1
% 15.31/2.47  --splitting_mode                        input
% 15.31/2.47  --splitting_grd                         true
% 15.31/2.47  --splitting_cvd                         false
% 15.31/2.47  --splitting_cvd_svl                     false
% 15.31/2.47  --splitting_nvd                         32
% 15.31/2.47  --sub_typing                            true
% 15.31/2.47  --prep_gs_sim                           true
% 15.31/2.47  --prep_unflatten                        true
% 15.31/2.47  --prep_res_sim                          true
% 15.31/2.47  --prep_upred                            true
% 15.31/2.47  --prep_sem_filter                       exhaustive
% 15.31/2.47  --prep_sem_filter_out                   false
% 15.31/2.47  --pred_elim                             true
% 15.31/2.47  --res_sim_input                         true
% 15.31/2.47  --eq_ax_congr_red                       true
% 15.31/2.47  --pure_diseq_elim                       true
% 15.31/2.47  --brand_transform                       false
% 15.31/2.47  --non_eq_to_eq                          false
% 15.31/2.47  --prep_def_merge                        true
% 15.31/2.47  --prep_def_merge_prop_impl              false
% 15.31/2.47  --prep_def_merge_mbd                    true
% 15.31/2.47  --prep_def_merge_tr_red                 false
% 15.31/2.47  --prep_def_merge_tr_cl                  false
% 15.31/2.47  --smt_preprocessing                     true
% 15.31/2.47  --smt_ac_axioms                         fast
% 15.31/2.47  --preprocessed_out                      false
% 15.31/2.47  --preprocessed_stats                    false
% 15.31/2.47  
% 15.31/2.47  ------ Abstraction refinement Options
% 15.31/2.47  
% 15.31/2.47  --abstr_ref                             []
% 15.31/2.47  --abstr_ref_prep                        false
% 15.31/2.47  --abstr_ref_until_sat                   false
% 15.31/2.47  --abstr_ref_sig_restrict                funpre
% 15.31/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 15.31/2.47  --abstr_ref_under                       []
% 15.31/2.47  
% 15.31/2.47  ------ SAT Options
% 15.31/2.47  
% 15.31/2.47  --sat_mode                              false
% 15.31/2.47  --sat_fm_restart_options                ""
% 15.31/2.47  --sat_gr_def                            false
% 15.31/2.47  --sat_epr_types                         true
% 15.31/2.47  --sat_non_cyclic_types                  false
% 15.31/2.47  --sat_finite_models                     false
% 15.31/2.47  --sat_fm_lemmas                         false
% 15.31/2.47  --sat_fm_prep                           false
% 15.31/2.47  --sat_fm_uc_incr                        true
% 15.31/2.47  --sat_out_model                         small
% 15.31/2.47  --sat_out_clauses                       false
% 15.31/2.47  
% 15.31/2.47  ------ QBF Options
% 15.31/2.47  
% 15.31/2.47  --qbf_mode                              false
% 15.31/2.47  --qbf_elim_univ                         false
% 15.31/2.47  --qbf_dom_inst                          none
% 15.31/2.47  --qbf_dom_pre_inst                      false
% 15.31/2.47  --qbf_sk_in                             false
% 15.31/2.47  --qbf_pred_elim                         true
% 15.31/2.47  --qbf_split                             512
% 15.31/2.47  
% 15.31/2.47  ------ BMC1 Options
% 15.31/2.47  
% 15.31/2.47  --bmc1_incremental                      false
% 15.31/2.47  --bmc1_axioms                           reachable_all
% 15.31/2.47  --bmc1_min_bound                        0
% 15.31/2.47  --bmc1_max_bound                        -1
% 15.31/2.47  --bmc1_max_bound_default                -1
% 15.31/2.47  --bmc1_symbol_reachability              true
% 15.31/2.47  --bmc1_property_lemmas                  false
% 15.31/2.47  --bmc1_k_induction                      false
% 15.31/2.47  --bmc1_non_equiv_states                 false
% 15.31/2.47  --bmc1_deadlock                         false
% 15.31/2.47  --bmc1_ucm                              false
% 15.31/2.47  --bmc1_add_unsat_core                   none
% 15.31/2.47  --bmc1_unsat_core_children              false
% 15.31/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 15.31/2.47  --bmc1_out_stat                         full
% 15.31/2.47  --bmc1_ground_init                      false
% 15.31/2.47  --bmc1_pre_inst_next_state              false
% 15.31/2.47  --bmc1_pre_inst_state                   false
% 15.31/2.47  --bmc1_pre_inst_reach_state             false
% 15.31/2.47  --bmc1_out_unsat_core                   false
% 15.31/2.47  --bmc1_aig_witness_out                  false
% 15.31/2.47  --bmc1_verbose                          false
% 15.31/2.47  --bmc1_dump_clauses_tptp                false
% 15.31/2.47  --bmc1_dump_unsat_core_tptp             false
% 15.31/2.47  --bmc1_dump_file                        -
% 15.31/2.47  --bmc1_ucm_expand_uc_limit              128
% 15.31/2.47  --bmc1_ucm_n_expand_iterations          6
% 15.31/2.47  --bmc1_ucm_extend_mode                  1
% 15.31/2.47  --bmc1_ucm_init_mode                    2
% 15.31/2.47  --bmc1_ucm_cone_mode                    none
% 15.31/2.47  --bmc1_ucm_reduced_relation_type        0
% 15.31/2.47  --bmc1_ucm_relax_model                  4
% 15.31/2.47  --bmc1_ucm_full_tr_after_sat            true
% 15.31/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 15.31/2.47  --bmc1_ucm_layered_model                none
% 15.31/2.47  --bmc1_ucm_max_lemma_size               10
% 15.31/2.47  
% 15.31/2.47  ------ AIG Options
% 15.31/2.47  
% 15.31/2.47  --aig_mode                              false
% 15.31/2.47  
% 15.31/2.47  ------ Instantiation Options
% 15.31/2.47  
% 15.31/2.47  --instantiation_flag                    true
% 15.31/2.47  --inst_sos_flag                         true
% 15.31/2.47  --inst_sos_phase                        true
% 15.31/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.31/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.31/2.47  --inst_lit_sel_side                     none
% 15.31/2.47  --inst_solver_per_active                1400
% 15.31/2.47  --inst_solver_calls_frac                1.
% 15.31/2.47  --inst_passive_queue_type               priority_queues
% 15.31/2.47  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 15.31/2.47  --inst_passive_queues_freq              [25;2]
% 15.31/2.47  --inst_dismatching                      true
% 15.31/2.47  --inst_eager_unprocessed_to_passive     true
% 15.31/2.47  --inst_prop_sim_given                   true
% 15.31/2.47  --inst_prop_sim_new                     false
% 15.31/2.47  --inst_subs_new                         false
% 15.31/2.47  --inst_eq_res_simp                      false
% 15.31/2.47  --inst_subs_given                       false
% 15.31/2.47  --inst_orphan_elimination               true
% 15.31/2.47  --inst_learning_loop_flag               true
% 15.31/2.47  --inst_learning_start                   3000
% 15.31/2.47  --inst_learning_factor                  2
% 15.31/2.47  --inst_start_prop_sim_after_learn       3
% 15.31/2.47  --inst_sel_renew                        solver
% 15.31/2.47  --inst_lit_activity_flag                true
% 15.31/2.47  --inst_restr_to_given                   false
% 15.31/2.47  --inst_activity_threshold               500
% 15.31/2.47  --inst_out_proof                        true
% 15.31/2.47  
% 15.31/2.47  ------ Resolution Options
% 15.31/2.47  
% 15.31/2.47  --resolution_flag                       false
% 15.31/2.47  --res_lit_sel                           adaptive
% 15.31/2.47  --res_lit_sel_side                      none
% 15.31/2.47  --res_ordering                          kbo
% 15.31/2.47  --res_to_prop_solver                    active
% 15.31/2.47  --res_prop_simpl_new                    false
% 15.31/2.47  --res_prop_simpl_given                  true
% 15.31/2.47  --res_passive_queue_type                priority_queues
% 15.31/2.47  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 15.31/2.47  --res_passive_queues_freq               [15;5]
% 15.31/2.47  --res_forward_subs                      full
% 15.31/2.47  --res_backward_subs                     full
% 15.31/2.47  --res_forward_subs_resolution           true
% 15.31/2.47  --res_backward_subs_resolution          true
% 15.31/2.47  --res_orphan_elimination                true
% 15.31/2.47  --res_time_limit                        2.
% 15.31/2.47  --res_out_proof                         true
% 15.31/2.47  
% 15.31/2.47  ------ Superposition Options
% 15.31/2.47  
% 15.31/2.47  --superposition_flag                    true
% 15.31/2.47  --sup_passive_queue_type                priority_queues
% 15.31/2.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.31/2.47  --sup_passive_queues_freq               [8;1;4]
% 15.31/2.47  --demod_completeness_check              fast
% 15.31/2.47  --demod_use_ground                      true
% 15.31/2.47  --sup_to_prop_solver                    passive
% 15.31/2.47  --sup_prop_simpl_new                    true
% 15.31/2.47  --sup_prop_simpl_given                  true
% 15.31/2.47  --sup_fun_splitting                     true
% 15.31/2.47  --sup_smt_interval                      50000
% 15.31/2.47  
% 15.31/2.47  ------ Superposition Simplification Setup
% 15.31/2.47  
% 15.31/2.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.31/2.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.31/2.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.31/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.31/2.47  --sup_full_triv                         [TrivRules;PropSubs]
% 15.31/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.31/2.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.31/2.47  --sup_immed_triv                        [TrivRules]
% 15.31/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.47  --sup_immed_bw_main                     []
% 15.31/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.31/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 15.31/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.31/2.47  --sup_input_bw                          []
% 15.31/2.47  
% 15.31/2.47  ------ Combination Options
% 15.31/2.47  
% 15.31/2.47  --comb_res_mult                         3
% 15.31/2.47  --comb_sup_mult                         2
% 15.31/2.47  --comb_inst_mult                        10
% 15.31/2.47  
% 15.31/2.47  ------ Debug Options
% 15.31/2.47  
% 15.31/2.47  --dbg_backtrace                         false
% 15.31/2.47  --dbg_dump_prop_clauses                 false
% 15.31/2.47  --dbg_dump_prop_clauses_file            -
% 15.31/2.47  --dbg_out_stat                          false
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  ------ Proving...
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  % SZS status Theorem for theBenchmark.p
% 15.31/2.47  
% 15.31/2.47   Resolution empty clause
% 15.31/2.47  
% 15.31/2.47  % SZS output start CNFRefutation for theBenchmark.p
% 15.31/2.47  
% 15.31/2.47  fof(f12,axiom,(
% 15.31/2.47    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f33,plain,(
% 15.31/2.47    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 15.31/2.47    inference(cnf_transformation,[],[f12])).
% 15.31/2.47  
% 15.31/2.47  fof(f11,axiom,(
% 15.31/2.47    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f32,plain,(
% 15.31/2.47    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f11])).
% 15.31/2.47  
% 15.31/2.47  fof(f9,axiom,(
% 15.31/2.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f30,plain,(
% 15.31/2.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.31/2.47    inference(cnf_transformation,[],[f9])).
% 15.31/2.47  
% 15.31/2.47  fof(f5,axiom,(
% 15.31/2.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f17,plain,(
% 15.31/2.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.31/2.47    inference(ennf_transformation,[],[f5])).
% 15.31/2.47  
% 15.31/2.47  fof(f26,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f17])).
% 15.31/2.47  
% 15.31/2.47  fof(f15,conjecture,(
% 15.31/2.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f16,negated_conjecture,(
% 15.31/2.47    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 15.31/2.47    inference(negated_conjecture,[],[f15])).
% 15.31/2.47  
% 15.31/2.47  fof(f18,plain,(
% 15.31/2.47    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 15.31/2.47    inference(ennf_transformation,[],[f16])).
% 15.31/2.47  
% 15.31/2.47  fof(f19,plain,(
% 15.31/2.47    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 15.31/2.47    inference(flattening,[],[f18])).
% 15.31/2.47  
% 15.31/2.47  fof(f20,plain,(
% 15.31/2.47    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 15.31/2.47    introduced(choice_axiom,[])).
% 15.31/2.47  
% 15.31/2.47  fof(f21,plain,(
% 15.31/2.47    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 15.31/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 15.31/2.47  
% 15.31/2.47  fof(f36,plain,(
% 15.31/2.47    r1_tarski(sK0,sK1)),
% 15.31/2.47    inference(cnf_transformation,[],[f21])).
% 15.31/2.47  
% 15.31/2.47  fof(f14,axiom,(
% 15.31/2.47    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f35,plain,(
% 15.31/2.47    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 15.31/2.47    inference(cnf_transformation,[],[f14])).
% 15.31/2.47  
% 15.31/2.47  fof(f13,axiom,(
% 15.31/2.47    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f34,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f13])).
% 15.31/2.47  
% 15.31/2.47  fof(f2,axiom,(
% 15.31/2.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f23,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.31/2.47    inference(cnf_transformation,[],[f2])).
% 15.31/2.47  
% 15.31/2.47  fof(f39,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 15.31/2.47    inference(definition_unfolding,[],[f34,f23])).
% 15.31/2.47  
% 15.31/2.47  fof(f44,plain,(
% 15.31/2.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))) )),
% 15.31/2.47    inference(definition_unfolding,[],[f35,f23,f39,f23,f39,f23,f39])).
% 15.31/2.47  
% 15.31/2.47  fof(f3,axiom,(
% 15.31/2.47    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f24,plain,(
% 15.31/2.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f3])).
% 15.31/2.47  
% 15.31/2.47  fof(f1,axiom,(
% 15.31/2.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f22,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f1])).
% 15.31/2.47  
% 15.31/2.47  fof(f6,axiom,(
% 15.31/2.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f27,plain,(
% 15.31/2.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f6])).
% 15.31/2.47  
% 15.31/2.47  fof(f10,axiom,(
% 15.31/2.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f31,plain,(
% 15.31/2.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.31/2.47    inference(cnf_transformation,[],[f10])).
% 15.31/2.47  
% 15.31/2.47  fof(f43,plain,(
% 15.31/2.47    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 15.31/2.47    inference(definition_unfolding,[],[f31,f39])).
% 15.31/2.47  
% 15.31/2.47  fof(f7,axiom,(
% 15.31/2.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f28,plain,(
% 15.31/2.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.31/2.47    inference(cnf_transformation,[],[f7])).
% 15.31/2.47  
% 15.31/2.47  fof(f41,plain,(
% 15.31/2.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 15.31/2.47    inference(definition_unfolding,[],[f28,f23,f23])).
% 15.31/2.47  
% 15.31/2.47  fof(f8,axiom,(
% 15.31/2.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 15.31/2.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.31/2.47  
% 15.31/2.47  fof(f29,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 15.31/2.47    inference(cnf_transformation,[],[f8])).
% 15.31/2.47  
% 15.31/2.47  fof(f42,plain,(
% 15.31/2.47    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0) )),
% 15.31/2.47    inference(definition_unfolding,[],[f29,f39,f23])).
% 15.31/2.47  
% 15.31/2.47  fof(f37,plain,(
% 15.31/2.47    r1_tarski(sK2,sK1)),
% 15.31/2.47    inference(cnf_transformation,[],[f21])).
% 15.31/2.47  
% 15.31/2.47  fof(f38,plain,(
% 15.31/2.47    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 15.31/2.47    inference(cnf_transformation,[],[f21])).
% 15.31/2.47  
% 15.31/2.47  cnf(c_10,plain,
% 15.31/2.47      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.31/2.47      inference(cnf_transformation,[],[f33]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_9,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.31/2.47      inference(cnf_transformation,[],[f32]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_326,plain,
% 15.31/2.47      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_10,c_9]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1599,plain,
% 15.31/2.47      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_10,c_326]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_7,plain,
% 15.31/2.47      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.31/2.47      inference(cnf_transformation,[],[f30]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1637,plain,
% 15.31/2.47      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_1599,c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_3,plain,
% 15.31/2.47      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.31/2.47      inference(cnf_transformation,[],[f26]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_14,negated_conjecture,
% 15.31/2.47      ( r1_tarski(sK0,sK1) ),
% 15.31/2.47      inference(cnf_transformation,[],[f36]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_101,plain,
% 15.31/2.47      ( k3_xboole_0(X0,X1) = X0 | sK1 != X1 | sK0 != X0 ),
% 15.31/2.47      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_102,plain,
% 15.31/2.47      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 15.31/2.47      inference(unflattening,[status(thm)],[c_101]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_11,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 15.31/2.47      inference(cnf_transformation,[],[f44]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1,plain,
% 15.31/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 15.31/2.47      inference(cnf_transformation,[],[f24]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_0,plain,
% 15.31/2.47      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.31/2.47      inference(cnf_transformation,[],[f22]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_143,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X2))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X0,X2)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X2,k5_xboole_0(X0,X1))) ),
% 15.31/2.47      inference(theory_normalisation,[status(thm)],[c_11,c_1,c_0]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1420,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))))))) = k5_xboole_0(k5_xboole_0(X0,sK0),k3_xboole_0(sK1,k5_xboole_0(X0,sK0))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_102,c_143]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_2098,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1)))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK0),k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK0))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_1637,c_1420]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4,plain,
% 15.31/2.47      ( r1_tarski(k1_xboole_0,X0) ),
% 15.31/2.47      inference(cnf_transformation,[],[f27]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_84,plain,
% 15.31/2.47      ( X0 != X1 | k3_xboole_0(X2,X1) = X2 | k1_xboole_0 != X2 ),
% 15.31/2.47      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_85,plain,
% 15.31/2.47      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.31/2.47      inference(unflattening,[status(thm)],[c_84]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_142,plain,
% 15.31/2.47      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.31/2.47      inference(theory_normalisation,[status(thm)],[c_85,c_1,c_0]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_389,plain,
% 15.31/2.47      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_142,c_0]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1440,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))))),k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))))),k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_389,c_143]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1454,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0)))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k1_xboole_0))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X0))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_389,c_143]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1483,plain,
% 15.31/2.47      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X0))) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_1454,c_7,c_389]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1497,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))))),k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))))))))) = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_1440,c_1483]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1498,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))))),k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))))))))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_1497,c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_325,plain,
% 15.31/2.47      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_7,c_9]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1499,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))),k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)))))))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_1498,c_7,c_325,c_389]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1500,plain,
% 15.31/2.47      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_1499,c_7,c_389]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1501,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_1500,c_1483]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_2120,plain,
% 15.31/2.47      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
% 15.31/2.47      inference(demodulation,
% 15.31/2.47                [status(thm)],
% 15.31/2.47                [c_2098,c_7,c_10,c_102,c_142,c_389,c_1501,c_1637]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_2121,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_2120,c_389]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_8,plain,
% 15.31/2.47      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 15.31/2.47      inference(cnf_transformation,[],[f43]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_90,plain,
% 15.31/2.47      ( X0 != X1
% 15.31/2.47      | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) != X3
% 15.31/2.47      | k3_xboole_0(X1,X3) = X1 ),
% 15.31/2.47      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_91,plain,
% 15.31/2.47      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 15.31/2.47      inference(unflattening,[status(thm)],[c_90]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_141,plain,
% 15.31/2.47      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 15.31/2.47      inference(theory_normalisation,[status(thm)],[c_91,c_1,c_0]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_692,plain,
% 15.31/2.47      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_142,c_141]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_706,plain,
% 15.31/2.47      ( k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_692,c_325]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_707,plain,
% 15.31/2.47      ( k3_xboole_0(X0,X0) = X0 ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_706,c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_786,plain,
% 15.31/2.47      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_707,c_1]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1809,plain,
% 15.31/2.47      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_0,c_786]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_5,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.31/2.47      inference(cnf_transformation,[],[f41]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_145,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.31/2.47      inference(theory_normalisation,[status(thm)],[c_5,c_1,c_0]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4273,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_1809,c_145]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4377,plain,
% 15.31/2.47      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_4273,c_10]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_6,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0 ),
% 15.31/2.47      inference(cnf_transformation,[],[f42]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_144,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) = X0 ),
% 15.31/2.47      inference(theory_normalisation,[status(thm)],[c_6,c_1,c_0]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4495,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_4377,c_144]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4496,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)) = X0 ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_4495,c_142]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4497,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_4496,c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_7256,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_0,c_4497]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_15247,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)) = sK1 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_102,c_7256]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_15863,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,sK0),X0)) = k5_xboole_0(sK1,X0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_15247,c_9]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_20078,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,X0))) = k5_xboole_0(sK1,X0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_9,c_15863]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_27172,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_2121,c_20078]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_162,plain,
% 15.31/2.47      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_3138,plain,
% 15.31/2.47      ( k3_xboole_0(sK1,k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_102,c_162]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_3685,plain,
% 15.31/2.47      ( k3_xboole_0(sK0,sK0) = k3_xboole_0(sK1,sK0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_707,c_3138]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_3722,plain,
% 15.31/2.47      ( k3_xboole_0(sK1,sK0) = sK0 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_3685,c_707]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_27193,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(sK1,sK0) ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_27172,c_3722]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_27194,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,sK1) = k5_xboole_0(sK1,sK0) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_27193,c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_27230,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK0,X0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_27194,c_9]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_37780,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK0,X0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_27230,c_9]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4272,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_707,c_145]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_2860,plain,
% 15.31/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_786,c_1809]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_2896,plain,
% 15.31/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_2860,c_707]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4378,plain,
% 15.31/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_4272,c_2896]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_4379,plain,
% 15.31/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_4378,c_10]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_6974,plain,
% 15.31/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_0,c_4379]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_13553,plain,
% 15.31/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X0,X1)),k1_xboole_0))) = k3_xboole_0(X0,X1) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_6974,c_141]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_13588,plain,
% 15.31/2.47      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_13553,c_7,c_7256]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_13,negated_conjecture,
% 15.31/2.47      ( r1_tarski(sK2,sK1) ),
% 15.31/2.47      inference(cnf_transformation,[],[f37]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_96,plain,
% 15.31/2.47      ( k3_xboole_0(X0,X1) = X0 | sK1 != X1 | sK2 != X0 ),
% 15.31/2.47      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_97,plain,
% 15.31/2.47      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 15.31/2.47      inference(unflattening,[status(thm)],[c_96]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1419,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1))))),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))))))) = k5_xboole_0(k5_xboole_0(X0,sK2),k3_xboole_0(sK1,k5_xboole_0(X0,sK2))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_97,c_143]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_13828,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK1,k3_xboole_0(X0,sK1))))),k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK1,k3_xboole_0(X0,sK1)))))))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK1),sK2),k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(X0,sK1),sK2))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_13588,c_1419]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_13901,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,sK1),sK2),k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(X0,sK1),sK2))) = k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) ),
% 15.31/2.47      inference(demodulation,
% 15.31/2.47                [status(thm)],
% 15.31/2.47                [c_13828,c_7,c_10,c_97,c_142,c_1637,c_7256]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_14039,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_102,c_13901]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_14075,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))) ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_14039,c_102]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_15228,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))))) = k5_xboole_0(sK0,sK2) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_14075,c_7256]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_15246,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_97,c_7256]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_15375,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,sK2) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_15228,c_15246]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_15376,plain,
% 15.31/2.47      ( k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)),k5_xboole_0(sK0,sK0)) = k5_xboole_0(sK0,sK2) ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_15375,c_102]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_15377,plain,
% 15.31/2.47      ( k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) = k5_xboole_0(sK0,sK2) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_15376,c_7,c_10]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_12,negated_conjecture,
% 15.31/2.47      ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
% 15.31/2.47      inference(cnf_transformation,[],[f38]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_111,plain,
% 15.31/2.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != sK1
% 15.31/2.47      | k5_xboole_0(sK0,sK2) != X0 ),
% 15.31/2.47      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_112,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(sK0,sK2),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2)))) != sK1 ),
% 15.31/2.47      inference(unflattening,[status(thm)],[c_111]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_321,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK0,sK2))))) != sK1 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_9,c_112]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_15436,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK0,sK2)))) != sK1 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_15377,c_321]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_44915,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,sK2)))) != sK1 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_37780,c_15436]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1912,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1)))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2)))),k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK1))))))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK2))) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_1637,c_1419]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1934,plain,
% 15.31/2.47      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) ),
% 15.31/2.47      inference(demodulation,
% 15.31/2.47                [status(thm)],
% 15.31/2.47                [c_1912,c_7,c_10,c_97,c_142,c_389,c_1501,c_1637]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1935,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_1934,c_389]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_15776,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_15246,c_9]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_19991,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK2,X0))) = k5_xboole_0(sK1,X0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_9,c_15776]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_25514,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_1935,c_19991]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_3137,plain,
% 15.31/2.47      ( k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,sK2) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_97,c_162]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_3589,plain,
% 15.31/2.47      ( k3_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_707,c_3137]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_3626,plain,
% 15.31/2.47      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_3589,c_707]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_25534,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) = k5_xboole_0(sK1,sK2) ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_25514,c_3626]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_25535,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,sK1) = k5_xboole_0(sK1,sK2) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_25534,c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_27217,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) = sK1 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_27194,c_15247]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_25562,plain,
% 15.31/2.47      ( k5_xboole_0(k5_xboole_0(sK2,sK1),X0) = k5_xboole_0(sK1,k5_xboole_0(sK2,X0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_25535,c_9]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_35873,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK2,X0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_25562,c_9]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_328,plain,
% 15.31/2.47      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_9,c_10]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_27170,plain,
% 15.31/2.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_328,c_20078]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_27198,plain,
% 15.31/2.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK0,X0))) = k5_xboole_0(sK0,sK1) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_27170,c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_43317,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(sK0,sK1) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_35873,c_27198]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_25512,plain,
% 15.31/2.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK2,X0))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_328,c_19991]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_25539,plain,
% 15.31/2.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK2,X0))) = k5_xboole_0(sK2,sK1) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_25512,c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_35819,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK0)) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_25539,c_20078]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_20080,plain,
% 15.31/2.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,sK0),X0))) = k5_xboole_0(sK0,k1_xboole_0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_328,c_15863]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_20107,plain,
% 15.31/2.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,sK0),X0))) = sK0 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_20080,c_7]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_28511,plain,
% 15.31/2.47      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(sK1,k5_xboole_0(sK0,X0)))) = sK0 ),
% 15.31/2.47      inference(light_normalisation,
% 15.31/2.47                [status(thm)],
% 15.31/2.47                [c_20107,c_20107,c_27194,c_27230]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_28536,plain,
% 15.31/2.47      ( k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(sK2,sK0) ),
% 15.31/2.47      inference(superposition,[status(thm)],[c_28511,c_19991]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_1638,plain,
% 15.31/2.47      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_1637,c_326]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_28541,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,sK0) = k5_xboole_0(sK0,sK2) ),
% 15.31/2.47      inference(demodulation,[status(thm)],[c_28536,c_1638]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_35821,plain,
% 15.31/2.47      ( k5_xboole_0(sK0,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_35819,c_28541]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_43320,plain,
% 15.31/2.47      ( k5_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK0,sK1) ),
% 15.31/2.47      inference(light_normalisation,[status(thm)],[c_43317,c_35821]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_44918,plain,
% 15.31/2.47      ( sK1 != sK1 ),
% 15.31/2.47      inference(light_normalisation,
% 15.31/2.47                [status(thm)],
% 15.31/2.47                [c_44915,c_25535,c_27217,c_43320]) ).
% 15.31/2.47  
% 15.31/2.47  cnf(c_44919,plain,
% 15.31/2.47      ( $false ),
% 15.31/2.47      inference(equality_resolution_simp,[status(thm)],[c_44918]) ).
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  % SZS output end CNFRefutation for theBenchmark.p
% 15.31/2.47  
% 15.31/2.47  ------                               Statistics
% 15.31/2.47  
% 15.31/2.47  ------ General
% 15.31/2.47  
% 15.31/2.47  abstr_ref_over_cycles:                  0
% 15.31/2.47  abstr_ref_under_cycles:                 0
% 15.31/2.47  gc_basic_clause_elim:                   0
% 15.31/2.47  forced_gc_time:                         0
% 15.31/2.47  parsing_time:                           0.008
% 15.31/2.47  unif_index_cands_time:                  0.
% 15.31/2.47  unif_index_add_time:                    0.
% 15.31/2.47  orderings_time:                         0.
% 15.31/2.47  out_proof_time:                         0.01
% 15.31/2.47  total_time:                             1.557
% 15.31/2.47  num_of_symbols:                         38
% 15.31/2.47  num_of_terms:                           83830
% 15.31/2.47  
% 15.31/2.47  ------ Preprocessing
% 15.31/2.47  
% 15.31/2.47  num_of_splits:                          0
% 15.31/2.47  num_of_split_atoms:                     0
% 15.31/2.47  num_of_reused_defs:                     0
% 15.31/2.47  num_eq_ax_congr_red:                    0
% 15.31/2.47  num_of_sem_filtered_clauses:            0
% 15.31/2.47  num_of_subtypes:                        0
% 15.31/2.47  monotx_restored_types:                  0
% 15.31/2.47  sat_num_of_epr_types:                   0
% 15.31/2.47  sat_num_of_non_cyclic_types:            0
% 15.31/2.47  sat_guarded_non_collapsed_types:        0
% 15.31/2.47  num_pure_diseq_elim:                    0
% 15.31/2.47  simp_replaced_by:                       0
% 15.31/2.47  res_preprocessed:                       36
% 15.31/2.47  prep_upred:                             0
% 15.31/2.47  prep_unflattend:                        10
% 15.31/2.47  smt_new_axioms:                         0
% 15.31/2.47  pred_elim_cands:                        1
% 15.31/2.47  pred_elim:                              1
% 15.31/2.47  pred_elim_cl:                           -2
% 15.31/2.47  pred_elim_cycles:                       2
% 15.31/2.47  merged_defs:                            0
% 15.31/2.47  merged_defs_ncl:                        0
% 15.31/2.47  bin_hyper_res:                          0
% 15.31/2.47  prep_cycles:                            2
% 15.31/2.47  pred_elim_time:                         0.
% 15.31/2.47  splitting_time:                         0.
% 15.31/2.47  sem_filter_time:                        0.
% 15.31/2.47  monotx_time:                            0.
% 15.31/2.47  subtype_inf_time:                       0.
% 15.31/2.47  
% 15.31/2.47  ------ Problem properties
% 15.31/2.47  
% 15.31/2.47  clauses:                                17
% 15.31/2.47  conjectures:                            0
% 15.31/2.47  epr:                                    0
% 15.31/2.47  horn:                                   17
% 15.31/2.47  ground:                                 5
% 15.31/2.47  unary:                                  15
% 15.31/2.47  binary:                                 2
% 15.31/2.47  lits:                                   19
% 15.31/2.47  lits_eq:                                19
% 15.31/2.47  fd_pure:                                0
% 15.31/2.47  fd_pseudo:                              0
% 15.31/2.47  fd_cond:                                0
% 15.31/2.47  fd_pseudo_cond:                         0
% 15.31/2.47  ac_symbols:                             1
% 15.31/2.47  
% 15.31/2.47  ------ Propositional Solver
% 15.31/2.47  
% 15.31/2.47  prop_solver_calls:                      25
% 15.31/2.47  prop_fast_solver_calls:                 452
% 15.31/2.47  smt_solver_calls:                       0
% 15.31/2.47  smt_fast_solver_calls:                  0
% 15.31/2.47  prop_num_of_clauses:                    12418
% 15.31/2.47  prop_preprocess_simplified:             11061
% 15.31/2.47  prop_fo_subsumed:                       0
% 15.31/2.47  prop_solver_time:                       0.
% 15.31/2.47  smt_solver_time:                        0.
% 15.31/2.47  smt_fast_solver_time:                   0.
% 15.31/2.47  prop_fast_solver_time:                  0.
% 15.31/2.47  prop_unsat_core_time:                   0.
% 15.31/2.47  
% 15.31/2.47  ------ QBF
% 15.31/2.47  
% 15.31/2.47  qbf_q_res:                              0
% 15.31/2.47  qbf_num_tautologies:                    0
% 15.31/2.47  qbf_prep_cycles:                        0
% 15.31/2.47  
% 15.31/2.47  ------ BMC1
% 15.31/2.47  
% 15.31/2.47  bmc1_current_bound:                     -1
% 15.31/2.47  bmc1_last_solved_bound:                 -1
% 15.31/2.47  bmc1_unsat_core_size:                   -1
% 15.31/2.47  bmc1_unsat_core_parents_size:           -1
% 15.31/2.47  bmc1_merge_next_fun:                    0
% 15.31/2.47  bmc1_unsat_core_clauses_time:           0.
% 15.31/2.47  
% 15.31/2.47  ------ Instantiation
% 15.31/2.47  
% 15.31/2.47  inst_num_of_clauses:                    3552
% 15.31/2.47  inst_num_in_passive:                    1001
% 15.31/2.47  inst_num_in_active:                     1301
% 15.31/2.47  inst_num_in_unprocessed:                1251
% 15.31/2.47  inst_num_of_loops:                      1400
% 15.31/2.47  inst_num_of_learning_restarts:          0
% 15.31/2.47  inst_num_moves_active_passive:          94
% 15.31/2.47  inst_lit_activity:                      0
% 15.31/2.47  inst_lit_activity_moves:                0
% 15.31/2.47  inst_num_tautologies:                   0
% 15.31/2.47  inst_num_prop_implied:                  0
% 15.31/2.47  inst_num_existing_simplified:           0
% 15.31/2.47  inst_num_eq_res_simplified:             0
% 15.31/2.47  inst_num_child_elim:                    0
% 15.31/2.47  inst_num_of_dismatching_blockings:      1851
% 15.31/2.47  inst_num_of_non_proper_insts:           4287
% 15.31/2.47  inst_num_of_duplicates:                 0
% 15.31/2.47  inst_inst_num_from_inst_to_res:         0
% 15.31/2.47  inst_dismatching_checking_time:         0.
% 15.31/2.47  
% 15.31/2.47  ------ Resolution
% 15.31/2.47  
% 15.31/2.47  res_num_of_clauses:                     0
% 15.31/2.47  res_num_in_passive:                     0
% 15.31/2.47  res_num_in_active:                      0
% 15.31/2.47  res_num_of_loops:                       38
% 15.31/2.47  res_forward_subset_subsumed:            640
% 15.31/2.47  res_backward_subset_subsumed:           6
% 15.31/2.47  res_forward_subsumed:                   0
% 15.31/2.47  res_backward_subsumed:                  0
% 15.31/2.47  res_forward_subsumption_resolution:     0
% 15.31/2.47  res_backward_subsumption_resolution:    0
% 15.31/2.47  res_clause_to_clause_subsumption:       42308
% 15.31/2.47  res_orphan_elimination:                 0
% 15.31/2.47  res_tautology_del:                      272
% 15.31/2.47  res_num_eq_res_simplified:              2
% 15.31/2.47  res_num_sel_changes:                    0
% 15.31/2.47  res_moves_from_active_to_pass:          0
% 15.31/2.47  
% 15.31/2.47  ------ Superposition
% 15.31/2.47  
% 15.31/2.47  sup_time_total:                         0.
% 15.31/2.47  sup_time_generating:                    0.
% 15.31/2.47  sup_time_sim_full:                      0.
% 15.31/2.47  sup_time_sim_immed:                     0.
% 15.31/2.47  
% 15.31/2.47  sup_num_of_clauses:                     4186
% 15.31/2.47  sup_num_in_active:                      203
% 15.31/2.47  sup_num_in_passive:                     3983
% 15.31/2.47  sup_num_of_loops:                       278
% 15.31/2.47  sup_fw_superposition:                   9751
% 15.31/2.47  sup_bw_superposition:                   8982
% 15.31/2.47  sup_immediate_simplified:               10544
% 15.31/2.47  sup_given_eliminated:                   8
% 15.31/2.47  comparisons_done:                       0
% 15.31/2.47  comparisons_avoided:                    0
% 15.31/2.47  
% 15.31/2.47  ------ Simplifications
% 15.31/2.47  
% 15.31/2.47  
% 15.31/2.47  sim_fw_subset_subsumed:                 0
% 15.31/2.47  sim_bw_subset_subsumed:                 0
% 15.31/2.47  sim_fw_subsumed:                        948
% 15.31/2.47  sim_bw_subsumed:                        50
% 15.31/2.47  sim_fw_subsumption_res:                 0
% 15.31/2.47  sim_bw_subsumption_res:                 0
% 15.31/2.47  sim_tautology_del:                      0
% 15.31/2.47  sim_eq_tautology_del:                   3469
% 15.31/2.47  sim_eq_res_simp:                        2
% 15.31/2.47  sim_fw_demodulated:                     8123
% 15.31/2.47  sim_bw_demodulated:                     249
% 15.31/2.47  sim_light_normalised:                   3925
% 15.31/2.47  sim_joinable_taut:                      695
% 15.31/2.47  sim_joinable_simp:                      0
% 15.31/2.47  sim_ac_normalised:                      0
% 15.31/2.47  sim_smt_subsumption:                    0
% 15.31/2.47  
%------------------------------------------------------------------------------
