%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:54 EST 2020

% Result     : Theorem 15.78s
% Output     : CNFRefutation 15.78s
% Verified   : 
% Statistics : Number of formulae       :  133 (12435 expanded)
%              Number of clauses        :  100 (5552 expanded)
%              Number of leaves         :   11 (2630 expanded)
%              Depth                    :   33
%              Number of atoms          :  177 (20035 expanded)
%              Number of equality atoms :  128 (10971 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f16])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f31,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_140,plain,
    ( X0 != X1
    | k3_xboole_0(X1,X2) = X1
    | k2_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_141,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_140])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_74,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_146,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) = k1_xboole_0
    | k2_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_74,c_9])).

cnf(c_147,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_1434,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_147])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_719,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_141])).

cnf(c_809,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_719])).

cnf(c_1448,plain,
    ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1434,c_809])).

cnf(c_1455,plain,
    ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1448,c_1434])).

cnf(c_1456,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1455,c_3])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1527,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1456,c_1])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_157,plain,
    ( k3_xboole_0(X0,X1) = X0
    | k2_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_158,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_6,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_394,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_1965,plain,
    ( k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0)) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_158,c_394])).

cnf(c_398,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_2700,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)),k3_xboole_0(X1,k2_xboole_0(sK1,sK2))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(sK0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_1965,c_398])).

cnf(c_4110,plain,
    ( k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),X0)) = k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1527,c_2700])).

cnf(c_1449,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1434,c_8])).

cnf(c_1454,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1449,c_3])).

cnf(c_4145,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)) ),
    inference(demodulation,[status(thm)],[c_4110,c_1454,c_1965])).

cnf(c_4269,plain,
    ( k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),X0))) ),
    inference(superposition,[status(thm)],[c_4145,c_1965])).

cnf(c_4474,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_141,c_4269])).

cnf(c_4517,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)) ),
    inference(demodulation,[status(thm)],[c_4474,c_1965])).

cnf(c_4717,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))) ),
    inference(superposition,[status(thm)],[c_4517,c_1965])).

cnf(c_1442,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_147,c_8])).

cnf(c_4033,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1442,c_1454])).

cnf(c_4702,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))) = k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)),sK0) ),
    inference(superposition,[status(thm)],[c_4517,c_4033])).

cnf(c_4741,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)),sK0) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)) ),
    inference(demodulation,[status(thm)],[c_4702,c_4517])).

cnf(c_4237,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)),sK0) = k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_4145,c_4033])).

cnf(c_4742,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)) = k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4741,c_141,c_4237])).

cnf(c_4830,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_4717,c_4742])).

cnf(c_4831,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))) = k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4830,c_1965,c_4742])).

cnf(c_5678,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4831,c_1965])).

cnf(c_5692,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))) = k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5678,c_1965,c_4742])).

cnf(c_6496,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5692,c_1965])).

cnf(c_6510,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))))) = k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6496,c_1965,c_4742])).

cnf(c_1518,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1454,c_0])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_125,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_126,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_125])).

cnf(c_396,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_126,c_6])).

cnf(c_573,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_396])).

cnf(c_657,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_573,c_158])).

cnf(c_1600,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_1518,c_657])).

cnf(c_1435,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_147])).

cnf(c_3950,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X1,X2),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_1435])).

cnf(c_8418,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X2),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_3950])).

cnf(c_10103,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,X0),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1600,c_8418])).

cnf(c_49010,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,sK1),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6510,c_10103])).

cnf(c_722,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_141])).

cnf(c_9718,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X1,X2),X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_722])).

cnf(c_16253,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)),k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),X1),k2_xboole_0(sK1,sK2))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_1965,c_9718])).

cnf(c_1975,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_394])).

cnf(c_11486,plain,
    ( k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0)) = k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_158,c_1975])).

cnf(c_16400,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)),k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),X1),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_16253,c_11486])).

cnf(c_24256,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))))),k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),X0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))),k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_6510,c_16400])).

cnf(c_11432,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_6510,c_1965])).

cnf(c_11447,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))))) = k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11432,c_1965,c_4742])).

cnf(c_24326,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))),k2_xboole_0(sK1,sK2))) = k3_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),X0),k2_xboole_0(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_24256,c_11447])).

cnf(c_9731,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_719,c_722])).

cnf(c_11495,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_719,c_1975])).

cnf(c_811,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_719,c_6])).

cnf(c_721,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_141])).

cnf(c_797,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_721,c_6])).

cnf(c_800,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_797,c_141])).

cnf(c_817,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = X0 ),
    inference(demodulation,[status(thm)],[c_811,c_800])).

cnf(c_21315,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X3)) = k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) ),
    inference(superposition,[status(thm)],[c_817,c_394])).

cnf(c_24327,plain,
    ( k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),X0),sK2),k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_24326,c_6510,c_9731,c_11495,c_21315])).

cnf(c_1581,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_1518,c_396])).

cnf(c_16018,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_800,c_1581])).

cnf(c_16044,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16018,c_126])).

cnf(c_17416,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_16044])).

cnf(c_1994,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_394,c_0])).

cnf(c_17515,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(sK0,X1)) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_17416,c_1994])).

cnf(c_17516,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(X1,sK0)) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_17416,c_398])).

cnf(c_17517,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(X1,sK0)) = k2_xboole_0(k3_xboole_0(X1,k3_xboole_0(X0,sK2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_17416,c_1975])).

cnf(c_17522,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(X1,sK0)) = k3_xboole_0(X1,k3_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_17517,c_1454])).

cnf(c_17523,plain,
    ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) = k3_xboole_0(X1,k3_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_17516,c_17522])).

cnf(c_17524,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_17515,c_17523])).

cnf(c_24328,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_24327,c_800,c_17524])).

cnf(c_49824,plain,
    ( k4_xboole_0(sK0,k3_xboole_0(sK1,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_49010,c_24328])).

cnf(c_49825,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_49824,c_721])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_72,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_152,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_72,c_10])).

cnf(c_153,plain,
    ( k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49825,c_153])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:49:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.78/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.78/2.49  
% 15.78/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.78/2.49  
% 15.78/2.49  ------  iProver source info
% 15.78/2.49  
% 15.78/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.78/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.78/2.49  git: non_committed_changes: false
% 15.78/2.49  git: last_make_outside_of_git: false
% 15.78/2.49  
% 15.78/2.49  ------ 
% 15.78/2.49  
% 15.78/2.49  ------ Input Options
% 15.78/2.49  
% 15.78/2.49  --out_options                           all
% 15.78/2.49  --tptp_safe_out                         true
% 15.78/2.49  --problem_path                          ""
% 15.78/2.49  --include_path                          ""
% 15.78/2.49  --clausifier                            res/vclausify_rel
% 15.78/2.49  --clausifier_options                    ""
% 15.78/2.49  --stdin                                 false
% 15.78/2.49  --stats_out                             all
% 15.78/2.49  
% 15.78/2.49  ------ General Options
% 15.78/2.49  
% 15.78/2.49  --fof                                   false
% 15.78/2.49  --time_out_real                         305.
% 15.78/2.49  --time_out_virtual                      -1.
% 15.78/2.49  --symbol_type_check                     false
% 15.78/2.49  --clausify_out                          false
% 15.78/2.49  --sig_cnt_out                           false
% 15.78/2.49  --trig_cnt_out                          false
% 15.78/2.49  --trig_cnt_out_tolerance                1.
% 15.78/2.49  --trig_cnt_out_sk_spl                   false
% 15.78/2.49  --abstr_cl_out                          false
% 15.78/2.49  
% 15.78/2.49  ------ Global Options
% 15.78/2.49  
% 15.78/2.49  --schedule                              default
% 15.78/2.49  --add_important_lit                     false
% 15.78/2.49  --prop_solver_per_cl                    1000
% 15.78/2.49  --min_unsat_core                        false
% 15.78/2.49  --soft_assumptions                      false
% 15.78/2.49  --soft_lemma_size                       3
% 15.78/2.49  --prop_impl_unit_size                   0
% 15.78/2.49  --prop_impl_unit                        []
% 15.78/2.49  --share_sel_clauses                     true
% 15.78/2.49  --reset_solvers                         false
% 15.78/2.49  --bc_imp_inh                            [conj_cone]
% 15.78/2.49  --conj_cone_tolerance                   3.
% 15.78/2.49  --extra_neg_conj                        none
% 15.78/2.49  --large_theory_mode                     true
% 15.78/2.49  --prolific_symb_bound                   200
% 15.78/2.49  --lt_threshold                          2000
% 15.78/2.49  --clause_weak_htbl                      true
% 15.78/2.49  --gc_record_bc_elim                     false
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing Options
% 15.78/2.49  
% 15.78/2.49  --preprocessing_flag                    true
% 15.78/2.49  --time_out_prep_mult                    0.1
% 15.78/2.49  --splitting_mode                        input
% 15.78/2.49  --splitting_grd                         true
% 15.78/2.49  --splitting_cvd                         false
% 15.78/2.49  --splitting_cvd_svl                     false
% 15.78/2.49  --splitting_nvd                         32
% 15.78/2.49  --sub_typing                            true
% 15.78/2.49  --prep_gs_sim                           true
% 15.78/2.49  --prep_unflatten                        true
% 15.78/2.49  --prep_res_sim                          true
% 15.78/2.49  --prep_upred                            true
% 15.78/2.49  --prep_sem_filter                       exhaustive
% 15.78/2.49  --prep_sem_filter_out                   false
% 15.78/2.49  --pred_elim                             true
% 15.78/2.49  --res_sim_input                         true
% 15.78/2.49  --eq_ax_congr_red                       true
% 15.78/2.49  --pure_diseq_elim                       true
% 15.78/2.49  --brand_transform                       false
% 15.78/2.49  --non_eq_to_eq                          false
% 15.78/2.49  --prep_def_merge                        true
% 15.78/2.49  --prep_def_merge_prop_impl              false
% 15.78/2.49  --prep_def_merge_mbd                    true
% 15.78/2.49  --prep_def_merge_tr_red                 false
% 15.78/2.49  --prep_def_merge_tr_cl                  false
% 15.78/2.49  --smt_preprocessing                     true
% 15.78/2.49  --smt_ac_axioms                         fast
% 15.78/2.49  --preprocessed_out                      false
% 15.78/2.49  --preprocessed_stats                    false
% 15.78/2.49  
% 15.78/2.49  ------ Abstraction refinement Options
% 15.78/2.49  
% 15.78/2.49  --abstr_ref                             []
% 15.78/2.49  --abstr_ref_prep                        false
% 15.78/2.49  --abstr_ref_until_sat                   false
% 15.78/2.49  --abstr_ref_sig_restrict                funpre
% 15.78/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.78/2.49  --abstr_ref_under                       []
% 15.78/2.49  
% 15.78/2.49  ------ SAT Options
% 15.78/2.49  
% 15.78/2.49  --sat_mode                              false
% 15.78/2.49  --sat_fm_restart_options                ""
% 15.78/2.49  --sat_gr_def                            false
% 15.78/2.49  --sat_epr_types                         true
% 15.78/2.49  --sat_non_cyclic_types                  false
% 15.78/2.49  --sat_finite_models                     false
% 15.78/2.49  --sat_fm_lemmas                         false
% 15.78/2.49  --sat_fm_prep                           false
% 15.78/2.49  --sat_fm_uc_incr                        true
% 15.78/2.49  --sat_out_model                         small
% 15.78/2.49  --sat_out_clauses                       false
% 15.78/2.49  
% 15.78/2.49  ------ QBF Options
% 15.78/2.49  
% 15.78/2.49  --qbf_mode                              false
% 15.78/2.49  --qbf_elim_univ                         false
% 15.78/2.49  --qbf_dom_inst                          none
% 15.78/2.49  --qbf_dom_pre_inst                      false
% 15.78/2.49  --qbf_sk_in                             false
% 15.78/2.49  --qbf_pred_elim                         true
% 15.78/2.49  --qbf_split                             512
% 15.78/2.49  
% 15.78/2.49  ------ BMC1 Options
% 15.78/2.49  
% 15.78/2.49  --bmc1_incremental                      false
% 15.78/2.49  --bmc1_axioms                           reachable_all
% 15.78/2.49  --bmc1_min_bound                        0
% 15.78/2.49  --bmc1_max_bound                        -1
% 15.78/2.49  --bmc1_max_bound_default                -1
% 15.78/2.49  --bmc1_symbol_reachability              true
% 15.78/2.49  --bmc1_property_lemmas                  false
% 15.78/2.49  --bmc1_k_induction                      false
% 15.78/2.49  --bmc1_non_equiv_states                 false
% 15.78/2.49  --bmc1_deadlock                         false
% 15.78/2.49  --bmc1_ucm                              false
% 15.78/2.49  --bmc1_add_unsat_core                   none
% 15.78/2.49  --bmc1_unsat_core_children              false
% 15.78/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.78/2.49  --bmc1_out_stat                         full
% 15.78/2.49  --bmc1_ground_init                      false
% 15.78/2.49  --bmc1_pre_inst_next_state              false
% 15.78/2.49  --bmc1_pre_inst_state                   false
% 15.78/2.49  --bmc1_pre_inst_reach_state             false
% 15.78/2.49  --bmc1_out_unsat_core                   false
% 15.78/2.49  --bmc1_aig_witness_out                  false
% 15.78/2.49  --bmc1_verbose                          false
% 15.78/2.49  --bmc1_dump_clauses_tptp                false
% 15.78/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.78/2.49  --bmc1_dump_file                        -
% 15.78/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.78/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.78/2.49  --bmc1_ucm_extend_mode                  1
% 15.78/2.49  --bmc1_ucm_init_mode                    2
% 15.78/2.49  --bmc1_ucm_cone_mode                    none
% 15.78/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.78/2.49  --bmc1_ucm_relax_model                  4
% 15.78/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.78/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.78/2.49  --bmc1_ucm_layered_model                none
% 15.78/2.49  --bmc1_ucm_max_lemma_size               10
% 15.78/2.49  
% 15.78/2.49  ------ AIG Options
% 15.78/2.49  
% 15.78/2.49  --aig_mode                              false
% 15.78/2.49  
% 15.78/2.49  ------ Instantiation Options
% 15.78/2.49  
% 15.78/2.49  --instantiation_flag                    true
% 15.78/2.49  --inst_sos_flag                         true
% 15.78/2.49  --inst_sos_phase                        true
% 15.78/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.78/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.78/2.49  --inst_lit_sel_side                     num_symb
% 15.78/2.49  --inst_solver_per_active                1400
% 15.78/2.49  --inst_solver_calls_frac                1.
% 15.78/2.49  --inst_passive_queue_type               priority_queues
% 15.78/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.78/2.49  --inst_passive_queues_freq              [25;2]
% 15.78/2.49  --inst_dismatching                      true
% 15.78/2.49  --inst_eager_unprocessed_to_passive     true
% 15.78/2.49  --inst_prop_sim_given                   true
% 15.78/2.49  --inst_prop_sim_new                     false
% 15.78/2.49  --inst_subs_new                         false
% 15.78/2.49  --inst_eq_res_simp                      false
% 15.78/2.49  --inst_subs_given                       false
% 15.78/2.49  --inst_orphan_elimination               true
% 15.78/2.49  --inst_learning_loop_flag               true
% 15.78/2.49  --inst_learning_start                   3000
% 15.78/2.49  --inst_learning_factor                  2
% 15.78/2.49  --inst_start_prop_sim_after_learn       3
% 15.78/2.49  --inst_sel_renew                        solver
% 15.78/2.49  --inst_lit_activity_flag                true
% 15.78/2.49  --inst_restr_to_given                   false
% 15.78/2.49  --inst_activity_threshold               500
% 15.78/2.49  --inst_out_proof                        true
% 15.78/2.49  
% 15.78/2.49  ------ Resolution Options
% 15.78/2.49  
% 15.78/2.49  --resolution_flag                       true
% 15.78/2.49  --res_lit_sel                           adaptive
% 15.78/2.49  --res_lit_sel_side                      none
% 15.78/2.49  --res_ordering                          kbo
% 15.78/2.49  --res_to_prop_solver                    active
% 15.78/2.49  --res_prop_simpl_new                    false
% 15.78/2.49  --res_prop_simpl_given                  true
% 15.78/2.49  --res_passive_queue_type                priority_queues
% 15.78/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.78/2.49  --res_passive_queues_freq               [15;5]
% 15.78/2.49  --res_forward_subs                      full
% 15.78/2.49  --res_backward_subs                     full
% 15.78/2.49  --res_forward_subs_resolution           true
% 15.78/2.49  --res_backward_subs_resolution          true
% 15.78/2.49  --res_orphan_elimination                true
% 15.78/2.49  --res_time_limit                        2.
% 15.78/2.49  --res_out_proof                         true
% 15.78/2.49  
% 15.78/2.49  ------ Superposition Options
% 15.78/2.49  
% 15.78/2.49  --superposition_flag                    true
% 15.78/2.49  --sup_passive_queue_type                priority_queues
% 15.78/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.78/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.78/2.49  --demod_completeness_check              fast
% 15.78/2.49  --demod_use_ground                      true
% 15.78/2.49  --sup_to_prop_solver                    passive
% 15.78/2.49  --sup_prop_simpl_new                    true
% 15.78/2.49  --sup_prop_simpl_given                  true
% 15.78/2.49  --sup_fun_splitting                     true
% 15.78/2.49  --sup_smt_interval                      50000
% 15.78/2.49  
% 15.78/2.49  ------ Superposition Simplification Setup
% 15.78/2.49  
% 15.78/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.78/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.78/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.78/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.78/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.78/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.78/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.78/2.49  --sup_immed_triv                        [TrivRules]
% 15.78/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_immed_bw_main                     []
% 15.78/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.78/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.78/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_input_bw                          []
% 15.78/2.49  
% 15.78/2.49  ------ Combination Options
% 15.78/2.49  
% 15.78/2.49  --comb_res_mult                         3
% 15.78/2.49  --comb_sup_mult                         2
% 15.78/2.49  --comb_inst_mult                        10
% 15.78/2.49  
% 15.78/2.49  ------ Debug Options
% 15.78/2.49  
% 15.78/2.49  --dbg_backtrace                         false
% 15.78/2.49  --dbg_dump_prop_clauses                 false
% 15.78/2.49  --dbg_dump_prop_clauses_file            -
% 15.78/2.49  --dbg_out_stat                          false
% 15.78/2.49  ------ Parsing...
% 15.78/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.78/2.49  ------ Proving...
% 15.78/2.49  ------ Problem Properties 
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  clauses                                 14
% 15.78/2.49  conjectures                             0
% 15.78/2.49  EPR                                     0
% 15.78/2.49  Horn                                    14
% 15.78/2.49  unary                                   12
% 15.78/2.49  binary                                  2
% 15.78/2.49  lits                                    16
% 15.78/2.49  lits eq                                 16
% 15.78/2.49  fd_pure                                 0
% 15.78/2.49  fd_pseudo                               0
% 15.78/2.49  fd_cond                                 0
% 15.78/2.49  fd_pseudo_cond                          0
% 15.78/2.49  AC symbols                              0
% 15.78/2.49  
% 15.78/2.49  ------ Schedule dynamic 5 is on 
% 15.78/2.49  
% 15.78/2.49  ------ no conjectures: strip conj schedule 
% 15.78/2.49  
% 15.78/2.49  ------ pure equality problem: resolution off 
% 15.78/2.49  
% 15.78/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  ------ 
% 15.78/2.49  Current options:
% 15.78/2.49  ------ 
% 15.78/2.49  
% 15.78/2.49  ------ Input Options
% 15.78/2.49  
% 15.78/2.49  --out_options                           all
% 15.78/2.49  --tptp_safe_out                         true
% 15.78/2.49  --problem_path                          ""
% 15.78/2.49  --include_path                          ""
% 15.78/2.49  --clausifier                            res/vclausify_rel
% 15.78/2.49  --clausifier_options                    ""
% 15.78/2.49  --stdin                                 false
% 15.78/2.49  --stats_out                             all
% 15.78/2.49  
% 15.78/2.49  ------ General Options
% 15.78/2.49  
% 15.78/2.49  --fof                                   false
% 15.78/2.49  --time_out_real                         305.
% 15.78/2.49  --time_out_virtual                      -1.
% 15.78/2.49  --symbol_type_check                     false
% 15.78/2.49  --clausify_out                          false
% 15.78/2.49  --sig_cnt_out                           false
% 15.78/2.49  --trig_cnt_out                          false
% 15.78/2.49  --trig_cnt_out_tolerance                1.
% 15.78/2.49  --trig_cnt_out_sk_spl                   false
% 15.78/2.49  --abstr_cl_out                          false
% 15.78/2.49  
% 15.78/2.49  ------ Global Options
% 15.78/2.49  
% 15.78/2.49  --schedule                              default
% 15.78/2.49  --add_important_lit                     false
% 15.78/2.49  --prop_solver_per_cl                    1000
% 15.78/2.49  --min_unsat_core                        false
% 15.78/2.49  --soft_assumptions                      false
% 15.78/2.49  --soft_lemma_size                       3
% 15.78/2.49  --prop_impl_unit_size                   0
% 15.78/2.49  --prop_impl_unit                        []
% 15.78/2.49  --share_sel_clauses                     true
% 15.78/2.49  --reset_solvers                         false
% 15.78/2.49  --bc_imp_inh                            [conj_cone]
% 15.78/2.49  --conj_cone_tolerance                   3.
% 15.78/2.49  --extra_neg_conj                        none
% 15.78/2.49  --large_theory_mode                     true
% 15.78/2.49  --prolific_symb_bound                   200
% 15.78/2.49  --lt_threshold                          2000
% 15.78/2.49  --clause_weak_htbl                      true
% 15.78/2.49  --gc_record_bc_elim                     false
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing Options
% 15.78/2.49  
% 15.78/2.49  --preprocessing_flag                    true
% 15.78/2.49  --time_out_prep_mult                    0.1
% 15.78/2.49  --splitting_mode                        input
% 15.78/2.49  --splitting_grd                         true
% 15.78/2.49  --splitting_cvd                         false
% 15.78/2.49  --splitting_cvd_svl                     false
% 15.78/2.49  --splitting_nvd                         32
% 15.78/2.49  --sub_typing                            true
% 15.78/2.49  --prep_gs_sim                           true
% 15.78/2.49  --prep_unflatten                        true
% 15.78/2.49  --prep_res_sim                          true
% 15.78/2.49  --prep_upred                            true
% 15.78/2.49  --prep_sem_filter                       exhaustive
% 15.78/2.49  --prep_sem_filter_out                   false
% 15.78/2.49  --pred_elim                             true
% 15.78/2.49  --res_sim_input                         true
% 15.78/2.49  --eq_ax_congr_red                       true
% 15.78/2.49  --pure_diseq_elim                       true
% 15.78/2.49  --brand_transform                       false
% 15.78/2.49  --non_eq_to_eq                          false
% 15.78/2.49  --prep_def_merge                        true
% 15.78/2.49  --prep_def_merge_prop_impl              false
% 15.78/2.49  --prep_def_merge_mbd                    true
% 15.78/2.49  --prep_def_merge_tr_red                 false
% 15.78/2.49  --prep_def_merge_tr_cl                  false
% 15.78/2.49  --smt_preprocessing                     true
% 15.78/2.49  --smt_ac_axioms                         fast
% 15.78/2.49  --preprocessed_out                      false
% 15.78/2.49  --preprocessed_stats                    false
% 15.78/2.49  
% 15.78/2.49  ------ Abstraction refinement Options
% 15.78/2.49  
% 15.78/2.49  --abstr_ref                             []
% 15.78/2.49  --abstr_ref_prep                        false
% 15.78/2.49  --abstr_ref_until_sat                   false
% 15.78/2.49  --abstr_ref_sig_restrict                funpre
% 15.78/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.78/2.49  --abstr_ref_under                       []
% 15.78/2.49  
% 15.78/2.49  ------ SAT Options
% 15.78/2.49  
% 15.78/2.49  --sat_mode                              false
% 15.78/2.49  --sat_fm_restart_options                ""
% 15.78/2.49  --sat_gr_def                            false
% 15.78/2.49  --sat_epr_types                         true
% 15.78/2.49  --sat_non_cyclic_types                  false
% 15.78/2.49  --sat_finite_models                     false
% 15.78/2.49  --sat_fm_lemmas                         false
% 15.78/2.49  --sat_fm_prep                           false
% 15.78/2.49  --sat_fm_uc_incr                        true
% 15.78/2.49  --sat_out_model                         small
% 15.78/2.49  --sat_out_clauses                       false
% 15.78/2.49  
% 15.78/2.49  ------ QBF Options
% 15.78/2.49  
% 15.78/2.49  --qbf_mode                              false
% 15.78/2.49  --qbf_elim_univ                         false
% 15.78/2.49  --qbf_dom_inst                          none
% 15.78/2.49  --qbf_dom_pre_inst                      false
% 15.78/2.49  --qbf_sk_in                             false
% 15.78/2.49  --qbf_pred_elim                         true
% 15.78/2.49  --qbf_split                             512
% 15.78/2.49  
% 15.78/2.49  ------ BMC1 Options
% 15.78/2.49  
% 15.78/2.49  --bmc1_incremental                      false
% 15.78/2.49  --bmc1_axioms                           reachable_all
% 15.78/2.49  --bmc1_min_bound                        0
% 15.78/2.49  --bmc1_max_bound                        -1
% 15.78/2.49  --bmc1_max_bound_default                -1
% 15.78/2.49  --bmc1_symbol_reachability              true
% 15.78/2.49  --bmc1_property_lemmas                  false
% 15.78/2.49  --bmc1_k_induction                      false
% 15.78/2.49  --bmc1_non_equiv_states                 false
% 15.78/2.49  --bmc1_deadlock                         false
% 15.78/2.49  --bmc1_ucm                              false
% 15.78/2.49  --bmc1_add_unsat_core                   none
% 15.78/2.49  --bmc1_unsat_core_children              false
% 15.78/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.78/2.49  --bmc1_out_stat                         full
% 15.78/2.49  --bmc1_ground_init                      false
% 15.78/2.49  --bmc1_pre_inst_next_state              false
% 15.78/2.49  --bmc1_pre_inst_state                   false
% 15.78/2.49  --bmc1_pre_inst_reach_state             false
% 15.78/2.49  --bmc1_out_unsat_core                   false
% 15.78/2.49  --bmc1_aig_witness_out                  false
% 15.78/2.49  --bmc1_verbose                          false
% 15.78/2.49  --bmc1_dump_clauses_tptp                false
% 15.78/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.78/2.49  --bmc1_dump_file                        -
% 15.78/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.78/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.78/2.49  --bmc1_ucm_extend_mode                  1
% 15.78/2.49  --bmc1_ucm_init_mode                    2
% 15.78/2.49  --bmc1_ucm_cone_mode                    none
% 15.78/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.78/2.49  --bmc1_ucm_relax_model                  4
% 15.78/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.78/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.78/2.49  --bmc1_ucm_layered_model                none
% 15.78/2.49  --bmc1_ucm_max_lemma_size               10
% 15.78/2.49  
% 15.78/2.49  ------ AIG Options
% 15.78/2.49  
% 15.78/2.49  --aig_mode                              false
% 15.78/2.49  
% 15.78/2.49  ------ Instantiation Options
% 15.78/2.49  
% 15.78/2.49  --instantiation_flag                    true
% 15.78/2.49  --inst_sos_flag                         true
% 15.78/2.49  --inst_sos_phase                        true
% 15.78/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.78/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.78/2.49  --inst_lit_sel_side                     none
% 15.78/2.49  --inst_solver_per_active                1400
% 15.78/2.49  --inst_solver_calls_frac                1.
% 15.78/2.49  --inst_passive_queue_type               priority_queues
% 15.78/2.49  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 15.78/2.49  --inst_passive_queues_freq              [25;2]
% 15.78/2.49  --inst_dismatching                      true
% 15.78/2.49  --inst_eager_unprocessed_to_passive     true
% 15.78/2.49  --inst_prop_sim_given                   true
% 15.78/2.49  --inst_prop_sim_new                     false
% 15.78/2.49  --inst_subs_new                         false
% 15.78/2.49  --inst_eq_res_simp                      false
% 15.78/2.49  --inst_subs_given                       false
% 15.78/2.49  --inst_orphan_elimination               true
% 15.78/2.49  --inst_learning_loop_flag               true
% 15.78/2.49  --inst_learning_start                   3000
% 15.78/2.49  --inst_learning_factor                  2
% 15.78/2.49  --inst_start_prop_sim_after_learn       3
% 15.78/2.49  --inst_sel_renew                        solver
% 15.78/2.49  --inst_lit_activity_flag                true
% 15.78/2.49  --inst_restr_to_given                   false
% 15.78/2.49  --inst_activity_threshold               500
% 15.78/2.49  --inst_out_proof                        true
% 15.78/2.49  
% 15.78/2.49  ------ Resolution Options
% 15.78/2.49  
% 15.78/2.49  --resolution_flag                       false
% 15.78/2.49  --res_lit_sel                           adaptive
% 15.78/2.49  --res_lit_sel_side                      none
% 15.78/2.49  --res_ordering                          kbo
% 15.78/2.49  --res_to_prop_solver                    active
% 15.78/2.49  --res_prop_simpl_new                    false
% 15.78/2.49  --res_prop_simpl_given                  true
% 15.78/2.49  --res_passive_queue_type                priority_queues
% 15.78/2.49  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 15.78/2.49  --res_passive_queues_freq               [15;5]
% 15.78/2.49  --res_forward_subs                      full
% 15.78/2.49  --res_backward_subs                     full
% 15.78/2.49  --res_forward_subs_resolution           true
% 15.78/2.49  --res_backward_subs_resolution          true
% 15.78/2.49  --res_orphan_elimination                true
% 15.78/2.49  --res_time_limit                        2.
% 15.78/2.49  --res_out_proof                         true
% 15.78/2.49  
% 15.78/2.49  ------ Superposition Options
% 15.78/2.49  
% 15.78/2.49  --superposition_flag                    true
% 15.78/2.49  --sup_passive_queue_type                priority_queues
% 15.78/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.78/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.78/2.49  --demod_completeness_check              fast
% 15.78/2.49  --demod_use_ground                      true
% 15.78/2.49  --sup_to_prop_solver                    passive
% 15.78/2.49  --sup_prop_simpl_new                    true
% 15.78/2.49  --sup_prop_simpl_given                  true
% 15.78/2.49  --sup_fun_splitting                     true
% 15.78/2.49  --sup_smt_interval                      50000
% 15.78/2.49  
% 15.78/2.49  ------ Superposition Simplification Setup
% 15.78/2.49  
% 15.78/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.78/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.78/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.78/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.78/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.78/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.78/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.78/2.49  --sup_immed_triv                        [TrivRules]
% 15.78/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_immed_bw_main                     []
% 15.78/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.78/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.78/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.78/2.49  --sup_input_bw                          []
% 15.78/2.49  
% 15.78/2.49  ------ Combination Options
% 15.78/2.49  
% 15.78/2.49  --comb_res_mult                         3
% 15.78/2.49  --comb_sup_mult                         2
% 15.78/2.49  --comb_inst_mult                        10
% 15.78/2.49  
% 15.78/2.49  ------ Debug Options
% 15.78/2.49  
% 15.78/2.49  --dbg_backtrace                         false
% 15.78/2.49  --dbg_dump_prop_clauses                 false
% 15.78/2.49  --dbg_dump_prop_clauses_file            -
% 15.78/2.49  --dbg_out_stat                          false
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  ------ Proving...
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  % SZS status Theorem for theBenchmark.p
% 15.78/2.49  
% 15.78/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.78/2.49  
% 15.78/2.49  fof(f7,axiom,(
% 15.78/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f15,plain,(
% 15.78/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.78/2.49    inference(ennf_transformation,[],[f7])).
% 15.78/2.49  
% 15.78/2.49  fof(f28,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f15])).
% 15.78/2.49  
% 15.78/2.49  fof(f9,axiom,(
% 15.78/2.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f30,plain,(
% 15.78/2.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.78/2.49    inference(cnf_transformation,[],[f9])).
% 15.78/2.49  
% 15.78/2.49  fof(f4,axiom,(
% 15.78/2.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f12,plain,(
% 15.78/2.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 15.78/2.49    inference(rectify,[],[f4])).
% 15.78/2.49  
% 15.78/2.49  fof(f24,plain,(
% 15.78/2.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 15.78/2.49    inference(cnf_transformation,[],[f12])).
% 15.78/2.49  
% 15.78/2.49  fof(f5,axiom,(
% 15.78/2.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f18,plain,(
% 15.78/2.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 15.78/2.49    inference(nnf_transformation,[],[f5])).
% 15.78/2.49  
% 15.78/2.49  fof(f26,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f18])).
% 15.78/2.49  
% 15.78/2.49  fof(f8,axiom,(
% 15.78/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f29,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.78/2.49    inference(cnf_transformation,[],[f8])).
% 15.78/2.49  
% 15.78/2.49  fof(f1,axiom,(
% 15.78/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f21,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f1])).
% 15.78/2.49  
% 15.78/2.49  fof(f2,axiom,(
% 15.78/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f22,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f2])).
% 15.78/2.49  
% 15.78/2.49  fof(f10,conjecture,(
% 15.78/2.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f11,negated_conjecture,(
% 15.78/2.49    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 15.78/2.49    inference(negated_conjecture,[],[f10])).
% 15.78/2.49  
% 15.78/2.49  fof(f16,plain,(
% 15.78/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 15.78/2.49    inference(ennf_transformation,[],[f11])).
% 15.78/2.49  
% 15.78/2.49  fof(f17,plain,(
% 15.78/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.78/2.49    inference(flattening,[],[f16])).
% 15.78/2.49  
% 15.78/2.49  fof(f19,plain,(
% 15.78/2.49    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 15.78/2.49    introduced(choice_axiom,[])).
% 15.78/2.49  
% 15.78/2.49  fof(f20,plain,(
% 15.78/2.49    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 15.78/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).
% 15.78/2.49  
% 15.78/2.49  fof(f31,plain,(
% 15.78/2.49    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 15.78/2.49    inference(cnf_transformation,[],[f20])).
% 15.78/2.49  
% 15.78/2.49  fof(f6,axiom,(
% 15.78/2.49    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f27,plain,(
% 15.78/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 15.78/2.49    inference(cnf_transformation,[],[f6])).
% 15.78/2.49  
% 15.78/2.49  fof(f3,axiom,(
% 15.78/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.78/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.78/2.49  
% 15.78/2.49  fof(f13,plain,(
% 15.78/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.78/2.49    inference(unused_predicate_definition_removal,[],[f3])).
% 15.78/2.49  
% 15.78/2.49  fof(f14,plain,(
% 15.78/2.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 15.78/2.49    inference(ennf_transformation,[],[f13])).
% 15.78/2.49  
% 15.78/2.49  fof(f23,plain,(
% 15.78/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f14])).
% 15.78/2.49  
% 15.78/2.49  fof(f32,plain,(
% 15.78/2.49    r1_xboole_0(sK0,sK2)),
% 15.78/2.49    inference(cnf_transformation,[],[f20])).
% 15.78/2.49  
% 15.78/2.49  fof(f25,plain,(
% 15.78/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 15.78/2.49    inference(cnf_transformation,[],[f18])).
% 15.78/2.49  
% 15.78/2.49  fof(f33,plain,(
% 15.78/2.49    ~r1_tarski(sK0,sK1)),
% 15.78/2.49    inference(cnf_transformation,[],[f20])).
% 15.78/2.49  
% 15.78/2.49  cnf(c_7,plain,
% 15.78/2.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.78/2.49      inference(cnf_transformation,[],[f28]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_9,plain,
% 15.78/2.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 15.78/2.49      inference(cnf_transformation,[],[f30]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_140,plain,
% 15.78/2.49      ( X0 != X1 | k3_xboole_0(X1,X2) = X1 | k2_xboole_0(X0,X3) != X2 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_141,plain,
% 15.78/2.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_140]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_3,plain,
% 15.78/2.49      ( k2_xboole_0(X0,X0) = X0 ),
% 15.78/2.49      inference(cnf_transformation,[],[f24]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4,plain,
% 15.78/2.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.78/2.49      inference(cnf_transformation,[],[f26]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_74,plain,
% 15.78/2.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.78/2.49      inference(prop_impl,[status(thm)],[c_4]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_146,plain,
% 15.78/2.49      ( X0 != X1
% 15.78/2.49      | k4_xboole_0(X1,X2) = k1_xboole_0
% 15.78/2.49      | k2_xboole_0(X0,X3) != X2 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_74,c_9]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_147,plain,
% 15.78/2.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_146]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1434,plain,
% 15.78/2.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_3,c_147]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_8,plain,
% 15.78/2.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.78/2.49      inference(cnf_transformation,[],[f29]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_0,plain,
% 15.78/2.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f21]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_719,plain,
% 15.78/2.49      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_0,c_141]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_809,plain,
% 15.78/2.49      ( k3_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X1) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_8,c_719]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1448,plain,
% 15.78/2.49      ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1434,c_809]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1455,plain,
% 15.78/2.49      ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) = k1_xboole_0 ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_1448,c_1434]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1456,plain,
% 15.78/2.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_1455,c_3]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1,plain,
% 15.78/2.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.78/2.49      inference(cnf_transformation,[],[f22]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1527,plain,
% 15.78/2.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1456,c_1]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_12,negated_conjecture,
% 15.78/2.49      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.78/2.49      inference(cnf_transformation,[],[f31]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_157,plain,
% 15.78/2.49      ( k3_xboole_0(X0,X1) = X0
% 15.78/2.49      | k2_xboole_0(sK1,sK2) != X1
% 15.78/2.49      | sK0 != X0 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_158,plain,
% 15.78/2.49      ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_157]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_6,plain,
% 15.78/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.78/2.49      inference(cnf_transformation,[],[f27]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_394,plain,
% 15.78/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1965,plain,
% 15.78/2.49      ( k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0)) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_158,c_394]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_398,plain,
% 15.78/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_2700,plain,
% 15.78/2.49      ( k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)),k3_xboole_0(X1,k2_xboole_0(sK1,sK2))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(sK0,X0),X1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1965,c_398]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4110,plain,
% 15.78/2.49      ( k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),X0)) = k2_xboole_0(k2_xboole_0(sK0,k1_xboole_0),k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1527,c_2700]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1449,plain,
% 15.78/2.49      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1434,c_8]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1454,plain,
% 15.78/2.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_1449,c_3]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4145,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_4110,c_1454,c_1965]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4269,plain,
% 15.78/2.49      ( k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),X0))) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_4145,c_1965]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4474,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_141,c_4269]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4517,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_4474,c_1965]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4717,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_4517,c_1965]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1442,plain,
% 15.78/2.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_147,c_8]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4033,plain,
% 15.78/2.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_1442,c_1454]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4702,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))) = k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)),sK0) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_4517,c_4033]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4741,plain,
% 15.78/2.49      ( k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)),sK0) = k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_4702,c_4517]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4237,plain,
% 15.78/2.49      ( k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)),sK0) = k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_4145,c_4033]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4742,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)) = k2_xboole_0(sK0,sK1) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_4741,c_141,c_4237]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4830,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_4717,c_4742]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_4831,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))) = k2_xboole_0(sK0,sK1) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_4830,c_1965,c_4742]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_5678,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_4831,c_1965]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_5692,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))) = k2_xboole_0(sK0,sK1) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_5678,c_1965,c_4742]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_6496,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_5692,c_1965]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_6510,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1)))))) = k2_xboole_0(sK0,sK1) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_6496,c_1965,c_4742]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1518,plain,
% 15.78/2.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1454,c_0]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_2,plain,
% 15.78/2.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.78/2.49      inference(cnf_transformation,[],[f23]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_11,negated_conjecture,
% 15.78/2.49      ( r1_xboole_0(sK0,sK2) ),
% 15.78/2.49      inference(cnf_transformation,[],[f32]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_125,plain,
% 15.78/2.49      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK2 != X1 | sK0 != X0 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_126,plain,
% 15.78/2.49      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_125]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_396,plain,
% 15.78/2.49      ( k3_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_126,c_6]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_573,plain,
% 15.78/2.49      ( k3_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_0,c_396]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_657,plain,
% 15.78/2.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK1)) = sK0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_573,c_158]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1600,plain,
% 15.78/2.49      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1518,c_657]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1435,plain,
% 15.78/2.49      ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_6,c_147]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_3950,plain,
% 15.78/2.49      ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X1,X2),X0)) = k1_xboole_0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1,c_1435]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_8418,plain,
% 15.78/2.49      ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X2),X1)) = k1_xboole_0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1,c_3950]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_10103,plain,
% 15.78/2.49      ( k4_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,X0),sK1)) = k1_xboole_0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1600,c_8418]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_49010,plain,
% 15.78/2.49      ( k4_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,sK1),sK1)) = k1_xboole_0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_6510,c_10103]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_722,plain,
% 15.78/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k3_xboole_0(X0,X1) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_6,c_141]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_9718,plain,
% 15.78/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X1,X2),X0)) = k3_xboole_0(X0,X1) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1,c_722]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_16253,plain,
% 15.78/2.49      ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)),k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),X1),k2_xboole_0(sK1,sK2))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1965,c_9718]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1975,plain,
% 15.78/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1,c_394]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_11486,plain,
% 15.78/2.49      ( k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,X0)) = k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_158,c_1975]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_16400,plain,
% 15.78/2.49      ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0)),k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,X0),X1),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k3_xboole_0(X0,k2_xboole_0(sK1,sK2))) ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_16253,c_11486]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_24256,plain,
% 15.78/2.49      ( k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))))),k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),X0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))),k2_xboole_0(sK1,sK2))) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_6510,c_16400]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_11432,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))))) = k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,sK1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_6510,c_1965]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_11447,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))))) = k2_xboole_0(sK0,sK1) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_11432,c_1965,c_4742]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_24326,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK1))))),k2_xboole_0(sK1,sK2))) = k3_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),X0),k2_xboole_0(sK1,sK2))) ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_24256,c_11447]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_9731,plain,
% 15.78/2.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_719,c_722]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_11495,plain,
% 15.78/2.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X0,X1))) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_719,c_1975]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_811,plain,
% 15.78/2.49      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_719,c_6]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_721,plain,
% 15.78/2.49      ( k3_xboole_0(X0,X0) = X0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_3,c_141]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_797,plain,
% 15.78/2.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_721,c_6]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_800,plain,
% 15.78/2.49      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_797,c_141]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_817,plain,
% 15.78/2.49      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = X0 ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_811,c_800]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_21315,plain,
% 15.78/2.49      ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X3)) = k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_817,c_394]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_24327,plain,
% 15.78/2.49      ( k2_xboole_0(sK1,k3_xboole_0(k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),X0),sK2),k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK0,sK1) ),
% 15.78/2.49      inference(demodulation,
% 15.78/2.49                [status(thm)],
% 15.78/2.49                [c_24326,c_6510,c_9731,c_11495,c_21315]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1581,plain,
% 15.78/2.49      ( k3_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK0,X0) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_1518,c_396]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_16018,plain,
% 15.78/2.49      ( k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK0,sK2) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_800,c_1581]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_16044,plain,
% 15.78/2.49      ( k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k1_xboole_0 ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_16018,c_126]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_17416,plain,
% 15.78/2.49      ( k3_xboole_0(sK0,k3_xboole_0(X0,sK2)) = k1_xboole_0 ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_1,c_16044]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_1994,plain,
% 15.78/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_394,c_0]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_17515,plain,
% 15.78/2.49      ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(sK0,X1)) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_17416,c_1994]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_17516,plain,
% 15.78/2.49      ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(X1,sK0)) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_17416,c_398]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_17517,plain,
% 15.78/2.49      ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(X1,sK0)) = k2_xboole_0(k3_xboole_0(X1,k3_xboole_0(X0,sK2)),k1_xboole_0) ),
% 15.78/2.49      inference(superposition,[status(thm)],[c_17416,c_1975]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_17522,plain,
% 15.78/2.49      ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(X1,sK0)) = k3_xboole_0(X1,k3_xboole_0(X0,sK2)) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_17517,c_1454]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_17523,plain,
% 15.78/2.49      ( k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) = k3_xboole_0(X1,k3_xboole_0(X0,sK2)) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_17516,c_17522]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_17524,plain,
% 15.78/2.49      ( k3_xboole_0(k3_xboole_0(X0,sK2),k2_xboole_0(sK0,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,sK2)) ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_17515,c_17523]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_24328,plain,
% 15.78/2.49      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_24327,c_800,c_17524]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_49824,plain,
% 15.78/2.49      ( k4_xboole_0(sK0,k3_xboole_0(sK1,sK1)) = k1_xboole_0 ),
% 15.78/2.49      inference(light_normalisation,[status(thm)],[c_49010,c_24328]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_49825,plain,
% 15.78/2.49      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 15.78/2.49      inference(demodulation,[status(thm)],[c_49824,c_721]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_5,plain,
% 15.78/2.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.78/2.49      inference(cnf_transformation,[],[f25]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_72,plain,
% 15.78/2.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.78/2.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_10,negated_conjecture,
% 15.78/2.49      ( ~ r1_tarski(sK0,sK1) ),
% 15.78/2.49      inference(cnf_transformation,[],[f33]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_152,plain,
% 15.78/2.49      ( k4_xboole_0(X0,X1) != k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 15.78/2.49      inference(resolution_lifted,[status(thm)],[c_72,c_10]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(c_153,plain,
% 15.78/2.49      ( k4_xboole_0(sK0,sK1) != k1_xboole_0 ),
% 15.78/2.49      inference(unflattening,[status(thm)],[c_152]) ).
% 15.78/2.49  
% 15.78/2.49  cnf(contradiction,plain,
% 15.78/2.49      ( $false ),
% 15.78/2.49      inference(minisat,[status(thm)],[c_49825,c_153]) ).
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.78/2.49  
% 15.78/2.49  ------                               Statistics
% 15.78/2.49  
% 15.78/2.49  ------ General
% 15.78/2.49  
% 15.78/2.49  abstr_ref_over_cycles:                  0
% 15.78/2.49  abstr_ref_under_cycles:                 0
% 15.78/2.49  gc_basic_clause_elim:                   0
% 15.78/2.49  forced_gc_time:                         0
% 15.78/2.49  parsing_time:                           0.007
% 15.78/2.49  unif_index_cands_time:                  0.
% 15.78/2.49  unif_index_add_time:                    0.
% 15.78/2.49  orderings_time:                         0.
% 15.78/2.49  out_proof_time:                         0.009
% 15.78/2.49  total_time:                             1.966
% 15.78/2.49  num_of_symbols:                         40
% 15.78/2.49  num_of_terms:                           80785
% 15.78/2.49  
% 15.78/2.49  ------ Preprocessing
% 15.78/2.49  
% 15.78/2.49  num_of_splits:                          0
% 15.78/2.49  num_of_split_atoms:                     0
% 15.78/2.49  num_of_reused_defs:                     0
% 15.78/2.49  num_eq_ax_congr_red:                    3
% 15.78/2.49  num_of_sem_filtered_clauses:            0
% 15.78/2.49  num_of_subtypes:                        0
% 15.78/2.49  monotx_restored_types:                  0
% 15.78/2.49  sat_num_of_epr_types:                   0
% 15.78/2.49  sat_num_of_non_cyclic_types:            0
% 15.78/2.49  sat_guarded_non_collapsed_types:        0
% 15.78/2.49  num_pure_diseq_elim:                    0
% 15.78/2.49  simp_replaced_by:                       0
% 15.78/2.49  res_preprocessed:                       32
% 15.78/2.49  prep_upred:                             0
% 15.78/2.49  prep_unflattend:                        13
% 15.78/2.49  smt_new_axioms:                         0
% 15.78/2.49  pred_elim_cands:                        2
% 15.78/2.49  pred_elim:                              2
% 15.78/2.49  pred_elim_cl:                           -1
% 15.78/2.49  pred_elim_cycles:                       3
% 15.78/2.49  merged_defs:                            2
% 15.78/2.49  merged_defs_ncl:                        0
% 15.78/2.49  bin_hyper_res:                          2
% 15.78/2.49  prep_cycles:                            2
% 15.78/2.49  pred_elim_time:                         0.001
% 15.78/2.49  splitting_time:                         0.
% 15.78/2.49  sem_filter_time:                        0.
% 15.78/2.49  monotx_time:                            0.
% 15.78/2.49  subtype_inf_time:                       0.
% 15.78/2.49  
% 15.78/2.49  ------ Problem properties
% 15.78/2.49  
% 15.78/2.49  clauses:                                14
% 15.78/2.49  conjectures:                            0
% 15.78/2.49  epr:                                    0
% 15.78/2.49  horn:                                   14
% 15.78/2.49  ground:                                 5
% 15.78/2.49  unary:                                  12
% 15.78/2.49  binary:                                 2
% 15.78/2.49  lits:                                   16
% 15.78/2.49  lits_eq:                                16
% 15.78/2.49  fd_pure:                                0
% 15.78/2.49  fd_pseudo:                              0
% 15.78/2.49  fd_cond:                                0
% 15.78/2.49  fd_pseudo_cond:                         0
% 15.78/2.49  ac_symbols:                             0
% 15.78/2.49  
% 15.78/2.49  ------ Propositional Solver
% 15.78/2.49  
% 15.78/2.49  prop_solver_calls:                      29
% 15.78/2.49  prop_fast_solver_calls:                 416
% 15.78/2.49  smt_solver_calls:                       0
% 15.78/2.49  smt_fast_solver_calls:                  0
% 15.78/2.49  prop_num_of_clauses:                    16166
% 15.78/2.49  prop_preprocess_simplified:             12395
% 15.78/2.49  prop_fo_subsumed:                       0
% 15.78/2.49  prop_solver_time:                       0.
% 15.78/2.49  smt_solver_time:                        0.
% 15.78/2.49  smt_fast_solver_time:                   0.
% 15.78/2.49  prop_fast_solver_time:                  0.
% 15.78/2.49  prop_unsat_core_time:                   0.001
% 15.78/2.49  
% 15.78/2.49  ------ QBF
% 15.78/2.49  
% 15.78/2.49  qbf_q_res:                              0
% 15.78/2.49  qbf_num_tautologies:                    0
% 15.78/2.49  qbf_prep_cycles:                        0
% 15.78/2.49  
% 15.78/2.49  ------ BMC1
% 15.78/2.49  
% 15.78/2.49  bmc1_current_bound:                     -1
% 15.78/2.49  bmc1_last_solved_bound:                 -1
% 15.78/2.49  bmc1_unsat_core_size:                   -1
% 15.78/2.49  bmc1_unsat_core_parents_size:           -1
% 15.78/2.49  bmc1_merge_next_fun:                    0
% 15.78/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.78/2.49  
% 15.78/2.49  ------ Instantiation
% 15.78/2.49  
% 15.78/2.49  inst_num_of_clauses:                    4391
% 15.78/2.49  inst_num_in_passive:                    1100
% 15.78/2.49  inst_num_in_active:                     1192
% 15.78/2.49  inst_num_in_unprocessed:                2099
% 15.78/2.49  inst_num_of_loops:                      1280
% 15.78/2.49  inst_num_of_learning_restarts:          0
% 15.78/2.49  inst_num_moves_active_passive:          82
% 15.78/2.49  inst_lit_activity:                      0
% 15.78/2.49  inst_lit_activity_moves:                0
% 15.78/2.49  inst_num_tautologies:                   0
% 15.78/2.49  inst_num_prop_implied:                  0
% 15.78/2.49  inst_num_existing_simplified:           0
% 15.78/2.49  inst_num_eq_res_simplified:             0
% 15.78/2.49  inst_num_child_elim:                    0
% 15.78/2.49  inst_num_of_dismatching_blockings:      1560
% 15.78/2.49  inst_num_of_non_proper_insts:           3718
% 15.78/2.49  inst_num_of_duplicates:                 0
% 15.78/2.49  inst_inst_num_from_inst_to_res:         0
% 15.78/2.49  inst_dismatching_checking_time:         0.
% 15.78/2.49  
% 15.78/2.49  ------ Resolution
% 15.78/2.49  
% 15.78/2.49  res_num_of_clauses:                     0
% 15.78/2.49  res_num_in_passive:                     0
% 15.78/2.49  res_num_in_active:                      0
% 15.78/2.49  res_num_of_loops:                       34
% 15.78/2.49  res_forward_subset_subsumed:            421
% 15.78/2.49  res_backward_subset_subsumed:           0
% 15.78/2.49  res_forward_subsumed:                   0
% 15.78/2.49  res_backward_subsumed:                  0
% 15.78/2.49  res_forward_subsumption_resolution:     0
% 15.78/2.49  res_backward_subsumption_resolution:    0
% 15.78/2.49  res_clause_to_clause_subsumption:       70354
% 15.78/2.49  res_orphan_elimination:                 0
% 15.78/2.49  res_tautology_del:                      168
% 15.78/2.49  res_num_eq_res_simplified:              1
% 15.78/2.49  res_num_sel_changes:                    0
% 15.78/2.49  res_moves_from_active_to_pass:          0
% 15.78/2.49  
% 15.78/2.49  ------ Superposition
% 15.78/2.49  
% 15.78/2.49  sup_time_total:                         0.
% 15.78/2.49  sup_time_generating:                    0.
% 15.78/2.49  sup_time_sim_full:                      0.
% 15.78/2.49  sup_time_sim_immed:                     0.
% 15.78/2.49  
% 15.78/2.49  sup_num_of_clauses:                     5554
% 15.78/2.49  sup_num_in_active:                      214
% 15.78/2.49  sup_num_in_passive:                     5340
% 15.78/2.49  sup_num_of_loops:                       255
% 15.78/2.49  sup_fw_superposition:                   12250
% 15.78/2.49  sup_bw_superposition:                   7285
% 15.78/2.49  sup_immediate_simplified:               11036
% 15.78/2.49  sup_given_eliminated:                   9
% 15.78/2.49  comparisons_done:                       0
% 15.78/2.49  comparisons_avoided:                    0
% 15.78/2.49  
% 15.78/2.49  ------ Simplifications
% 15.78/2.49  
% 15.78/2.49  
% 15.78/2.49  sim_fw_subset_subsumed:                 0
% 15.78/2.49  sim_bw_subset_subsumed:                 0
% 15.78/2.49  sim_fw_subsumed:                        1205
% 15.78/2.49  sim_bw_subsumed:                        85
% 15.78/2.49  sim_fw_subsumption_res:                 0
% 15.78/2.49  sim_bw_subsumption_res:                 0
% 15.78/2.49  sim_tautology_del:                      0
% 15.78/2.49  sim_eq_tautology_del:                   4639
% 15.78/2.49  sim_eq_res_simp:                        1
% 15.78/2.49  sim_fw_demodulated:                     7684
% 15.78/2.49  sim_bw_demodulated:                     206
% 15.78/2.49  sim_light_normalised:                   5353
% 15.78/2.49  sim_joinable_taut:                      0
% 15.78/2.49  sim_joinable_simp:                      0
% 15.78/2.49  sim_ac_normalised:                      0
% 15.78/2.49  sim_smt_subsumption:                    0
% 15.78/2.49  
%------------------------------------------------------------------------------
