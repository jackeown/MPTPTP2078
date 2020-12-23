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
% DateTime   : Thu Dec  3 11:25:55 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :  159 (5039 expanded)
%              Number of clauses        :  114 (1667 expanded)
%              Number of leaves         :   14 (1282 expanded)
%              Depth                    :   34
%              Number of atoms          :  223 (8065 expanded)
%              Number of equality atoms :  165 (4219 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f31,f25,f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f33,f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f35,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f35,f25])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f34,f25])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f29,f25,f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_80,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_141,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X0)) != X3
    | k3_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_80,c_11])).

cnf(c_142,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_141])).

cnf(c_895,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_142])).

cnf(c_4,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1058,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X0,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_895,c_4])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_202,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != X0
    | k3_xboole_0(X1,X0) = X1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_203,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_447,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_203,c_4])).

cnf(c_2495,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1))),k3_xboole_0(sK0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_1058])).

cnf(c_2874,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(sK0,k3_xboole_0(X0,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1058,c_2495])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2961,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X0,sK2)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2874,c_10])).

cnf(c_501,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_4,c_9])).

cnf(c_18666,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,sK2)))) = k5_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2961,c_501])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_285,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_8,c_4])).

cnf(c_3475,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2))) ),
    inference(superposition,[status(thm)],[c_5,c_285])).

cnf(c_461,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2)) = k3_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_503,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_5,c_9])).

cnf(c_3687,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_3475,c_461,c_503])).

cnf(c_18963,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_18666,c_10,c_3687])).

cnf(c_1032,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK0)),k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_203,c_895])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_283,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_5])).

cnf(c_1084,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1032,c_283])).

cnf(c_1033,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_895])).

cnf(c_1612,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1084,c_1033])).

cnf(c_1644,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0),k5_xboole_0(sK0,sK0)),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1612,c_203])).

cnf(c_1645,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1644,c_283])).

cnf(c_9280,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0),k1_xboole_0),k1_xboole_0)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1645,c_461])).

cnf(c_1614,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_142,c_1033])).

cnf(c_538,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_447,c_4])).

cnf(c_678,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_4,c_538])).

cnf(c_688,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_678,c_447])).

cnf(c_903,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,X1))),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_688,c_142])).

cnf(c_929,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_903,c_285,c_688])).

cnf(c_930,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_929,c_142])).

cnf(c_918,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_142,c_447])).

cnf(c_932,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_930,c_918])).

cnf(c_1641,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1614,c_932])).

cnf(c_1642,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1641,c_10])).

cnf(c_2271,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1642,c_4])).

cnf(c_2311,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_2271])).

cnf(c_2406,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2311,c_930])).

cnf(c_899,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_203,c_142])).

cnf(c_936,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_899,c_283])).

cnf(c_535,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_5,c_447])).

cnf(c_543,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_535,c_203])).

cnf(c_1598,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_1033])).

cnf(c_4662,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK0)),k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_543,c_1598])).

cnf(c_460,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_203,c_5])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_84,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_207,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_84,c_13])).

cnf(c_208,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_282,plain,
    ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_208,c_203])).

cnf(c_466,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_460,c_282])).

cnf(c_467,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_466,c_10])).

cnf(c_507,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),sK0)) ),
    inference(superposition,[status(thm)],[c_203,c_9])).

cnf(c_604,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,sK0),k3_xboole_0(k3_xboole_0(sK0,sK0),sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_203,c_507])).

cnf(c_610,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,sK0),k3_xboole_0(k3_xboole_0(sK0,sK0),sK0)) = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_604,c_283])).

cnf(c_677,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0))) = sK0 ),
    inference(superposition,[status(thm)],[c_610,c_5])).

cnf(c_1005,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_677,c_677,c_930])).

cnf(c_1006,plain,
    ( k3_xboole_0(sK0,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_1005,c_10])).

cnf(c_3536,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_1006,c_285])).

cnf(c_504,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_203,c_9])).

cnf(c_618,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_5,c_504])).

cnf(c_626,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_618,c_543])).

cnf(c_627,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_626,c_283])).

cnf(c_3596,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k3_xboole_0(sK0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_3536,c_627])).

cnf(c_3597,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3596,c_283,c_930])).

cnf(c_4780,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4662,c_5,c_283,c_467,c_3597])).

cnf(c_5402,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_936,c_4780])).

cnf(c_9510,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_9280,c_2406,c_5402])).

cnf(c_679,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_5,c_538])).

cnf(c_740,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_679,c_447])).

cnf(c_6919,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_2271,c_740])).

cnf(c_6961,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6919,c_10,c_930,c_2406,c_3597])).

cnf(c_7674,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_6961,c_4])).

cnf(c_7680,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6961,c_895])).

cnf(c_9511,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9510,c_10,c_7674,c_7680])).

cnf(c_9694,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9511,c_461])).

cnf(c_9763,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_9694,c_10])).

cnf(c_10115,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_9763,c_504])).

cnf(c_19232,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_18963,c_10115])).

cnf(c_19252,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_19232,c_18963])).

cnf(c_19253,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_19252,c_932])).

cnf(c_19254,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_19253,c_10])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_82,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_157,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_158,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_185,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | k5_xboole_0(X2,k3_xboole_0(X2,sK2)) != sK0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_82,c_158])).

cnf(c_186,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_448,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,sK2))) != sK0
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_186])).

cnf(c_451,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
    | k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) != sK0 ),
    inference(demodulation,[status(thm)],[c_448,c_285])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_78,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_147,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_78,c_12])).

cnf(c_148,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_194,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | k3_xboole_0(sK0,sK2) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_82,c_148])).

cnf(c_195,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
    | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_194])).

cnf(c_7485,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_195,c_932])).

cnf(c_19496,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19254,c_7485])).

cnf(c_19497,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19496,c_283])).

cnf(c_19498,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_19497])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.92/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.92/1.48  
% 7.92/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.92/1.48  
% 7.92/1.48  ------  iProver source info
% 7.92/1.48  
% 7.92/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.92/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.92/1.48  git: non_committed_changes: false
% 7.92/1.48  git: last_make_outside_of_git: false
% 7.92/1.48  
% 7.92/1.48  ------ 
% 7.92/1.48  
% 7.92/1.48  ------ Input Options
% 7.92/1.48  
% 7.92/1.48  --out_options                           all
% 7.92/1.48  --tptp_safe_out                         true
% 7.92/1.48  --problem_path                          ""
% 7.92/1.48  --include_path                          ""
% 7.92/1.48  --clausifier                            res/vclausify_rel
% 7.92/1.48  --clausifier_options                    ""
% 7.92/1.48  --stdin                                 false
% 7.92/1.48  --stats_out                             all
% 7.92/1.48  
% 7.92/1.48  ------ General Options
% 7.92/1.48  
% 7.92/1.48  --fof                                   false
% 7.92/1.48  --time_out_real                         305.
% 7.92/1.48  --time_out_virtual                      -1.
% 7.92/1.48  --symbol_type_check                     false
% 7.92/1.48  --clausify_out                          false
% 7.92/1.48  --sig_cnt_out                           false
% 7.92/1.48  --trig_cnt_out                          false
% 7.92/1.48  --trig_cnt_out_tolerance                1.
% 7.92/1.48  --trig_cnt_out_sk_spl                   false
% 7.92/1.48  --abstr_cl_out                          false
% 7.92/1.48  
% 7.92/1.48  ------ Global Options
% 7.92/1.48  
% 7.92/1.48  --schedule                              default
% 7.92/1.48  --add_important_lit                     false
% 7.92/1.48  --prop_solver_per_cl                    1000
% 7.92/1.48  --min_unsat_core                        false
% 7.92/1.48  --soft_assumptions                      false
% 7.92/1.48  --soft_lemma_size                       3
% 7.92/1.48  --prop_impl_unit_size                   0
% 7.92/1.48  --prop_impl_unit                        []
% 7.92/1.48  --share_sel_clauses                     true
% 7.92/1.48  --reset_solvers                         false
% 7.92/1.48  --bc_imp_inh                            [conj_cone]
% 7.92/1.48  --conj_cone_tolerance                   3.
% 7.92/1.48  --extra_neg_conj                        none
% 7.92/1.48  --large_theory_mode                     true
% 7.92/1.48  --prolific_symb_bound                   200
% 7.92/1.48  --lt_threshold                          2000
% 7.92/1.48  --clause_weak_htbl                      true
% 7.92/1.48  --gc_record_bc_elim                     false
% 7.92/1.48  
% 7.92/1.48  ------ Preprocessing Options
% 7.92/1.49  
% 7.92/1.49  --preprocessing_flag                    true
% 7.92/1.49  --time_out_prep_mult                    0.1
% 7.92/1.49  --splitting_mode                        input
% 7.92/1.49  --splitting_grd                         true
% 7.92/1.49  --splitting_cvd                         false
% 7.92/1.49  --splitting_cvd_svl                     false
% 7.92/1.49  --splitting_nvd                         32
% 7.92/1.49  --sub_typing                            true
% 7.92/1.49  --prep_gs_sim                           true
% 7.92/1.49  --prep_unflatten                        true
% 7.92/1.49  --prep_res_sim                          true
% 7.92/1.49  --prep_upred                            true
% 7.92/1.49  --prep_sem_filter                       exhaustive
% 7.92/1.49  --prep_sem_filter_out                   false
% 7.92/1.49  --pred_elim                             true
% 7.92/1.49  --res_sim_input                         true
% 7.92/1.49  --eq_ax_congr_red                       true
% 7.92/1.49  --pure_diseq_elim                       true
% 7.92/1.49  --brand_transform                       false
% 7.92/1.49  --non_eq_to_eq                          false
% 7.92/1.49  --prep_def_merge                        true
% 7.92/1.49  --prep_def_merge_prop_impl              false
% 7.92/1.49  --prep_def_merge_mbd                    true
% 7.92/1.49  --prep_def_merge_tr_red                 false
% 7.92/1.49  --prep_def_merge_tr_cl                  false
% 7.92/1.49  --smt_preprocessing                     true
% 7.92/1.49  --smt_ac_axioms                         fast
% 7.92/1.49  --preprocessed_out                      false
% 7.92/1.49  --preprocessed_stats                    false
% 7.92/1.49  
% 7.92/1.49  ------ Abstraction refinement Options
% 7.92/1.49  
% 7.92/1.49  --abstr_ref                             []
% 7.92/1.49  --abstr_ref_prep                        false
% 7.92/1.49  --abstr_ref_until_sat                   false
% 7.92/1.49  --abstr_ref_sig_restrict                funpre
% 7.92/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.92/1.49  --abstr_ref_under                       []
% 7.92/1.49  
% 7.92/1.49  ------ SAT Options
% 7.92/1.49  
% 7.92/1.49  --sat_mode                              false
% 7.92/1.49  --sat_fm_restart_options                ""
% 7.92/1.49  --sat_gr_def                            false
% 7.92/1.49  --sat_epr_types                         true
% 7.92/1.49  --sat_non_cyclic_types                  false
% 7.92/1.49  --sat_finite_models                     false
% 7.92/1.49  --sat_fm_lemmas                         false
% 7.92/1.49  --sat_fm_prep                           false
% 7.92/1.49  --sat_fm_uc_incr                        true
% 7.92/1.49  --sat_out_model                         small
% 7.92/1.49  --sat_out_clauses                       false
% 7.92/1.49  
% 7.92/1.49  ------ QBF Options
% 7.92/1.49  
% 7.92/1.49  --qbf_mode                              false
% 7.92/1.49  --qbf_elim_univ                         false
% 7.92/1.49  --qbf_dom_inst                          none
% 7.92/1.49  --qbf_dom_pre_inst                      false
% 7.92/1.49  --qbf_sk_in                             false
% 7.92/1.49  --qbf_pred_elim                         true
% 7.92/1.49  --qbf_split                             512
% 7.92/1.49  
% 7.92/1.49  ------ BMC1 Options
% 7.92/1.49  
% 7.92/1.49  --bmc1_incremental                      false
% 7.92/1.49  --bmc1_axioms                           reachable_all
% 7.92/1.49  --bmc1_min_bound                        0
% 7.92/1.49  --bmc1_max_bound                        -1
% 7.92/1.49  --bmc1_max_bound_default                -1
% 7.92/1.49  --bmc1_symbol_reachability              true
% 7.92/1.49  --bmc1_property_lemmas                  false
% 7.92/1.49  --bmc1_k_induction                      false
% 7.92/1.49  --bmc1_non_equiv_states                 false
% 7.92/1.49  --bmc1_deadlock                         false
% 7.92/1.49  --bmc1_ucm                              false
% 7.92/1.49  --bmc1_add_unsat_core                   none
% 7.92/1.49  --bmc1_unsat_core_children              false
% 7.92/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.92/1.49  --bmc1_out_stat                         full
% 7.92/1.49  --bmc1_ground_init                      false
% 7.92/1.49  --bmc1_pre_inst_next_state              false
% 7.92/1.49  --bmc1_pre_inst_state                   false
% 7.92/1.49  --bmc1_pre_inst_reach_state             false
% 7.92/1.49  --bmc1_out_unsat_core                   false
% 7.92/1.49  --bmc1_aig_witness_out                  false
% 7.92/1.49  --bmc1_verbose                          false
% 7.92/1.49  --bmc1_dump_clauses_tptp                false
% 7.92/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.92/1.49  --bmc1_dump_file                        -
% 7.92/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.92/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.92/1.49  --bmc1_ucm_extend_mode                  1
% 7.92/1.49  --bmc1_ucm_init_mode                    2
% 7.92/1.49  --bmc1_ucm_cone_mode                    none
% 7.92/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.92/1.49  --bmc1_ucm_relax_model                  4
% 7.92/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.92/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.92/1.49  --bmc1_ucm_layered_model                none
% 7.92/1.49  --bmc1_ucm_max_lemma_size               10
% 7.92/1.49  
% 7.92/1.49  ------ AIG Options
% 7.92/1.49  
% 7.92/1.49  --aig_mode                              false
% 7.92/1.49  
% 7.92/1.49  ------ Instantiation Options
% 7.92/1.49  
% 7.92/1.49  --instantiation_flag                    true
% 7.92/1.49  --inst_sos_flag                         true
% 7.92/1.49  --inst_sos_phase                        true
% 7.92/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.92/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.92/1.49  --inst_lit_sel_side                     num_symb
% 7.92/1.49  --inst_solver_per_active                1400
% 7.92/1.49  --inst_solver_calls_frac                1.
% 7.92/1.49  --inst_passive_queue_type               priority_queues
% 7.92/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.92/1.49  --inst_passive_queues_freq              [25;2]
% 7.92/1.49  --inst_dismatching                      true
% 7.92/1.49  --inst_eager_unprocessed_to_passive     true
% 7.92/1.49  --inst_prop_sim_given                   true
% 7.92/1.49  --inst_prop_sim_new                     false
% 7.92/1.49  --inst_subs_new                         false
% 7.92/1.49  --inst_eq_res_simp                      false
% 7.92/1.49  --inst_subs_given                       false
% 7.92/1.49  --inst_orphan_elimination               true
% 7.92/1.49  --inst_learning_loop_flag               true
% 7.92/1.49  --inst_learning_start                   3000
% 7.92/1.49  --inst_learning_factor                  2
% 7.92/1.49  --inst_start_prop_sim_after_learn       3
% 7.92/1.49  --inst_sel_renew                        solver
% 7.92/1.49  --inst_lit_activity_flag                true
% 7.92/1.49  --inst_restr_to_given                   false
% 7.92/1.49  --inst_activity_threshold               500
% 7.92/1.49  --inst_out_proof                        true
% 7.92/1.49  
% 7.92/1.49  ------ Resolution Options
% 7.92/1.49  
% 7.92/1.49  --resolution_flag                       true
% 7.92/1.49  --res_lit_sel                           adaptive
% 7.92/1.49  --res_lit_sel_side                      none
% 7.92/1.49  --res_ordering                          kbo
% 7.92/1.49  --res_to_prop_solver                    active
% 7.92/1.49  --res_prop_simpl_new                    false
% 7.92/1.49  --res_prop_simpl_given                  true
% 7.92/1.49  --res_passive_queue_type                priority_queues
% 7.92/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.92/1.49  --res_passive_queues_freq               [15;5]
% 7.92/1.49  --res_forward_subs                      full
% 7.92/1.49  --res_backward_subs                     full
% 7.92/1.49  --res_forward_subs_resolution           true
% 7.92/1.49  --res_backward_subs_resolution          true
% 7.92/1.49  --res_orphan_elimination                true
% 7.92/1.49  --res_time_limit                        2.
% 7.92/1.49  --res_out_proof                         true
% 7.92/1.49  
% 7.92/1.49  ------ Superposition Options
% 7.92/1.49  
% 7.92/1.49  --superposition_flag                    true
% 7.92/1.49  --sup_passive_queue_type                priority_queues
% 7.92/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.92/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.92/1.49  --demod_completeness_check              fast
% 7.92/1.49  --demod_use_ground                      true
% 7.92/1.49  --sup_to_prop_solver                    passive
% 7.92/1.49  --sup_prop_simpl_new                    true
% 7.92/1.49  --sup_prop_simpl_given                  true
% 7.92/1.49  --sup_fun_splitting                     true
% 7.92/1.49  --sup_smt_interval                      50000
% 7.92/1.49  
% 7.92/1.49  ------ Superposition Simplification Setup
% 7.92/1.49  
% 7.92/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.92/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.92/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.92/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.92/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.92/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.92/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.92/1.49  --sup_immed_triv                        [TrivRules]
% 7.92/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_immed_bw_main                     []
% 7.92/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.92/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.92/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_input_bw                          []
% 7.92/1.49  
% 7.92/1.49  ------ Combination Options
% 7.92/1.49  
% 7.92/1.49  --comb_res_mult                         3
% 7.92/1.49  --comb_sup_mult                         2
% 7.92/1.49  --comb_inst_mult                        10
% 7.92/1.49  
% 7.92/1.49  ------ Debug Options
% 7.92/1.49  
% 7.92/1.49  --dbg_backtrace                         false
% 7.92/1.49  --dbg_dump_prop_clauses                 false
% 7.92/1.49  --dbg_dump_prop_clauses_file            -
% 7.92/1.49  --dbg_out_stat                          false
% 7.92/1.49  ------ Parsing...
% 7.92/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.92/1.49  ------ Proving...
% 7.92/1.49  ------ Problem Properties 
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  clauses                                 15
% 7.92/1.49  conjectures                             0
% 7.92/1.49  EPR                                     0
% 7.92/1.49  Horn                                    15
% 7.92/1.49  unary                                   9
% 7.92/1.49  binary                                  4
% 7.92/1.49  lits                                    23
% 7.92/1.49  lits eq                                 21
% 7.92/1.49  fd_pure                                 0
% 7.92/1.49  fd_pseudo                               0
% 7.92/1.49  fd_cond                                 0
% 7.92/1.49  fd_pseudo_cond                          0
% 7.92/1.49  AC symbols                              0
% 7.92/1.49  
% 7.92/1.49  ------ Schedule dynamic 5 is on 
% 7.92/1.49  
% 7.92/1.49  ------ no conjectures: strip conj schedule 
% 7.92/1.49  
% 7.92/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ 
% 7.92/1.49  Current options:
% 7.92/1.49  ------ 
% 7.92/1.49  
% 7.92/1.49  ------ Input Options
% 7.92/1.49  
% 7.92/1.49  --out_options                           all
% 7.92/1.49  --tptp_safe_out                         true
% 7.92/1.49  --problem_path                          ""
% 7.92/1.49  --include_path                          ""
% 7.92/1.49  --clausifier                            res/vclausify_rel
% 7.92/1.49  --clausifier_options                    ""
% 7.92/1.49  --stdin                                 false
% 7.92/1.49  --stats_out                             all
% 7.92/1.49  
% 7.92/1.49  ------ General Options
% 7.92/1.49  
% 7.92/1.49  --fof                                   false
% 7.92/1.49  --time_out_real                         305.
% 7.92/1.49  --time_out_virtual                      -1.
% 7.92/1.49  --symbol_type_check                     false
% 7.92/1.49  --clausify_out                          false
% 7.92/1.49  --sig_cnt_out                           false
% 7.92/1.49  --trig_cnt_out                          false
% 7.92/1.49  --trig_cnt_out_tolerance                1.
% 7.92/1.49  --trig_cnt_out_sk_spl                   false
% 7.92/1.49  --abstr_cl_out                          false
% 7.92/1.49  
% 7.92/1.49  ------ Global Options
% 7.92/1.49  
% 7.92/1.49  --schedule                              default
% 7.92/1.49  --add_important_lit                     false
% 7.92/1.49  --prop_solver_per_cl                    1000
% 7.92/1.49  --min_unsat_core                        false
% 7.92/1.49  --soft_assumptions                      false
% 7.92/1.49  --soft_lemma_size                       3
% 7.92/1.49  --prop_impl_unit_size                   0
% 7.92/1.49  --prop_impl_unit                        []
% 7.92/1.49  --share_sel_clauses                     true
% 7.92/1.49  --reset_solvers                         false
% 7.92/1.49  --bc_imp_inh                            [conj_cone]
% 7.92/1.49  --conj_cone_tolerance                   3.
% 7.92/1.49  --extra_neg_conj                        none
% 7.92/1.49  --large_theory_mode                     true
% 7.92/1.49  --prolific_symb_bound                   200
% 7.92/1.49  --lt_threshold                          2000
% 7.92/1.49  --clause_weak_htbl                      true
% 7.92/1.49  --gc_record_bc_elim                     false
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing Options
% 7.92/1.49  
% 7.92/1.49  --preprocessing_flag                    true
% 7.92/1.49  --time_out_prep_mult                    0.1
% 7.92/1.49  --splitting_mode                        input
% 7.92/1.49  --splitting_grd                         true
% 7.92/1.49  --splitting_cvd                         false
% 7.92/1.49  --splitting_cvd_svl                     false
% 7.92/1.49  --splitting_nvd                         32
% 7.92/1.49  --sub_typing                            true
% 7.92/1.49  --prep_gs_sim                           true
% 7.92/1.49  --prep_unflatten                        true
% 7.92/1.49  --prep_res_sim                          true
% 7.92/1.49  --prep_upred                            true
% 7.92/1.49  --prep_sem_filter                       exhaustive
% 7.92/1.49  --prep_sem_filter_out                   false
% 7.92/1.49  --pred_elim                             true
% 7.92/1.49  --res_sim_input                         true
% 7.92/1.49  --eq_ax_congr_red                       true
% 7.92/1.49  --pure_diseq_elim                       true
% 7.92/1.49  --brand_transform                       false
% 7.92/1.49  --non_eq_to_eq                          false
% 7.92/1.49  --prep_def_merge                        true
% 7.92/1.49  --prep_def_merge_prop_impl              false
% 7.92/1.49  --prep_def_merge_mbd                    true
% 7.92/1.49  --prep_def_merge_tr_red                 false
% 7.92/1.49  --prep_def_merge_tr_cl                  false
% 7.92/1.49  --smt_preprocessing                     true
% 7.92/1.49  --smt_ac_axioms                         fast
% 7.92/1.49  --preprocessed_out                      false
% 7.92/1.49  --preprocessed_stats                    false
% 7.92/1.49  
% 7.92/1.49  ------ Abstraction refinement Options
% 7.92/1.49  
% 7.92/1.49  --abstr_ref                             []
% 7.92/1.49  --abstr_ref_prep                        false
% 7.92/1.49  --abstr_ref_until_sat                   false
% 7.92/1.49  --abstr_ref_sig_restrict                funpre
% 7.92/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.92/1.49  --abstr_ref_under                       []
% 7.92/1.49  
% 7.92/1.49  ------ SAT Options
% 7.92/1.49  
% 7.92/1.49  --sat_mode                              false
% 7.92/1.49  --sat_fm_restart_options                ""
% 7.92/1.49  --sat_gr_def                            false
% 7.92/1.49  --sat_epr_types                         true
% 7.92/1.49  --sat_non_cyclic_types                  false
% 7.92/1.49  --sat_finite_models                     false
% 7.92/1.49  --sat_fm_lemmas                         false
% 7.92/1.49  --sat_fm_prep                           false
% 7.92/1.49  --sat_fm_uc_incr                        true
% 7.92/1.49  --sat_out_model                         small
% 7.92/1.49  --sat_out_clauses                       false
% 7.92/1.49  
% 7.92/1.49  ------ QBF Options
% 7.92/1.49  
% 7.92/1.49  --qbf_mode                              false
% 7.92/1.49  --qbf_elim_univ                         false
% 7.92/1.49  --qbf_dom_inst                          none
% 7.92/1.49  --qbf_dom_pre_inst                      false
% 7.92/1.49  --qbf_sk_in                             false
% 7.92/1.49  --qbf_pred_elim                         true
% 7.92/1.49  --qbf_split                             512
% 7.92/1.49  
% 7.92/1.49  ------ BMC1 Options
% 7.92/1.49  
% 7.92/1.49  --bmc1_incremental                      false
% 7.92/1.49  --bmc1_axioms                           reachable_all
% 7.92/1.49  --bmc1_min_bound                        0
% 7.92/1.49  --bmc1_max_bound                        -1
% 7.92/1.49  --bmc1_max_bound_default                -1
% 7.92/1.49  --bmc1_symbol_reachability              true
% 7.92/1.49  --bmc1_property_lemmas                  false
% 7.92/1.49  --bmc1_k_induction                      false
% 7.92/1.49  --bmc1_non_equiv_states                 false
% 7.92/1.49  --bmc1_deadlock                         false
% 7.92/1.49  --bmc1_ucm                              false
% 7.92/1.49  --bmc1_add_unsat_core                   none
% 7.92/1.49  --bmc1_unsat_core_children              false
% 7.92/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.92/1.49  --bmc1_out_stat                         full
% 7.92/1.49  --bmc1_ground_init                      false
% 7.92/1.49  --bmc1_pre_inst_next_state              false
% 7.92/1.49  --bmc1_pre_inst_state                   false
% 7.92/1.49  --bmc1_pre_inst_reach_state             false
% 7.92/1.49  --bmc1_out_unsat_core                   false
% 7.92/1.49  --bmc1_aig_witness_out                  false
% 7.92/1.49  --bmc1_verbose                          false
% 7.92/1.49  --bmc1_dump_clauses_tptp                false
% 7.92/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.92/1.49  --bmc1_dump_file                        -
% 7.92/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.92/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.92/1.49  --bmc1_ucm_extend_mode                  1
% 7.92/1.49  --bmc1_ucm_init_mode                    2
% 7.92/1.49  --bmc1_ucm_cone_mode                    none
% 7.92/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.92/1.49  --bmc1_ucm_relax_model                  4
% 7.92/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.92/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.92/1.49  --bmc1_ucm_layered_model                none
% 7.92/1.49  --bmc1_ucm_max_lemma_size               10
% 7.92/1.49  
% 7.92/1.49  ------ AIG Options
% 7.92/1.49  
% 7.92/1.49  --aig_mode                              false
% 7.92/1.49  
% 7.92/1.49  ------ Instantiation Options
% 7.92/1.49  
% 7.92/1.49  --instantiation_flag                    true
% 7.92/1.49  --inst_sos_flag                         true
% 7.92/1.49  --inst_sos_phase                        true
% 7.92/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.92/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.92/1.49  --inst_lit_sel_side                     none
% 7.92/1.49  --inst_solver_per_active                1400
% 7.92/1.49  --inst_solver_calls_frac                1.
% 7.92/1.49  --inst_passive_queue_type               priority_queues
% 7.92/1.49  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 7.92/1.49  --inst_passive_queues_freq              [25;2]
% 7.92/1.49  --inst_dismatching                      true
% 7.92/1.49  --inst_eager_unprocessed_to_passive     true
% 7.92/1.49  --inst_prop_sim_given                   true
% 7.92/1.49  --inst_prop_sim_new                     false
% 7.92/1.49  --inst_subs_new                         false
% 7.92/1.49  --inst_eq_res_simp                      false
% 7.92/1.49  --inst_subs_given                       false
% 7.92/1.49  --inst_orphan_elimination               true
% 7.92/1.49  --inst_learning_loop_flag               true
% 7.92/1.49  --inst_learning_start                   3000
% 7.92/1.49  --inst_learning_factor                  2
% 7.92/1.49  --inst_start_prop_sim_after_learn       3
% 7.92/1.49  --inst_sel_renew                        solver
% 7.92/1.49  --inst_lit_activity_flag                true
% 7.92/1.49  --inst_restr_to_given                   false
% 7.92/1.49  --inst_activity_threshold               500
% 7.92/1.49  --inst_out_proof                        true
% 7.92/1.49  
% 7.92/1.49  ------ Resolution Options
% 7.92/1.49  
% 7.92/1.49  --resolution_flag                       false
% 7.92/1.49  --res_lit_sel                           adaptive
% 7.92/1.49  --res_lit_sel_side                      none
% 7.92/1.49  --res_ordering                          kbo
% 7.92/1.49  --res_to_prop_solver                    active
% 7.92/1.49  --res_prop_simpl_new                    false
% 7.92/1.49  --res_prop_simpl_given                  true
% 7.92/1.49  --res_passive_queue_type                priority_queues
% 7.92/1.49  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 7.92/1.49  --res_passive_queues_freq               [15;5]
% 7.92/1.49  --res_forward_subs                      full
% 7.92/1.49  --res_backward_subs                     full
% 7.92/1.49  --res_forward_subs_resolution           true
% 7.92/1.49  --res_backward_subs_resolution          true
% 7.92/1.49  --res_orphan_elimination                true
% 7.92/1.49  --res_time_limit                        2.
% 7.92/1.49  --res_out_proof                         true
% 7.92/1.49  
% 7.92/1.49  ------ Superposition Options
% 7.92/1.49  
% 7.92/1.49  --superposition_flag                    true
% 7.92/1.49  --sup_passive_queue_type                priority_queues
% 7.92/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.92/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.92/1.49  --demod_completeness_check              fast
% 7.92/1.49  --demod_use_ground                      true
% 7.92/1.49  --sup_to_prop_solver                    passive
% 7.92/1.49  --sup_prop_simpl_new                    true
% 7.92/1.49  --sup_prop_simpl_given                  true
% 7.92/1.49  --sup_fun_splitting                     true
% 7.92/1.49  --sup_smt_interval                      50000
% 7.92/1.49  
% 7.92/1.49  ------ Superposition Simplification Setup
% 7.92/1.49  
% 7.92/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.92/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.92/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.92/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.92/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.92/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.92/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.92/1.49  --sup_immed_triv                        [TrivRules]
% 7.92/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_immed_bw_main                     []
% 7.92/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.92/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.92/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_input_bw                          []
% 7.92/1.49  
% 7.92/1.49  ------ Combination Options
% 7.92/1.49  
% 7.92/1.49  --comb_res_mult                         3
% 7.92/1.49  --comb_sup_mult                         2
% 7.92/1.49  --comb_inst_mult                        10
% 7.92/1.49  
% 7.92/1.49  ------ Debug Options
% 7.92/1.49  
% 7.92/1.49  --dbg_backtrace                         false
% 7.92/1.49  --dbg_dump_prop_clauses                 false
% 7.92/1.49  --dbg_dump_prop_clauses_file            -
% 7.92/1.49  --dbg_out_stat                          false
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ Proving...
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  % SZS status Theorem for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49   Resolution empty clause
% 7.92/1.49  
% 7.92/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  fof(f9,axiom,(
% 7.92/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f31,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f9])).
% 7.92/1.49  
% 7.92/1.49  fof(f3,axiom,(
% 7.92/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f25,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f3])).
% 7.92/1.49  
% 7.92/1.49  fof(f43,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)))) )),
% 7.92/1.49    inference(definition_unfolding,[],[f31,f25,f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f1,axiom,(
% 7.92/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f17,plain,(
% 7.92/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.92/1.49    inference(nnf_transformation,[],[f1])).
% 7.92/1.49  
% 7.92/1.49  fof(f21,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f17])).
% 7.92/1.49  
% 7.92/1.49  fof(f11,axiom,(
% 7.92/1.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f33,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f11])).
% 7.92/1.49  
% 7.92/1.49  fof(f44,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 7.92/1.49    inference(definition_unfolding,[],[f33,f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f4,axiom,(
% 7.92/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f26,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f4])).
% 7.92/1.49  
% 7.92/1.49  fof(f6,axiom,(
% 7.92/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f15,plain,(
% 7.92/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.92/1.49    inference(ennf_transformation,[],[f6])).
% 7.92/1.49  
% 7.92/1.49  fof(f28,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f15])).
% 7.92/1.49  
% 7.92/1.49  fof(f13,conjecture,(
% 7.92/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f14,negated_conjecture,(
% 7.92/1.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.92/1.49    inference(negated_conjecture,[],[f13])).
% 7.92/1.49  
% 7.92/1.49  fof(f16,plain,(
% 7.92/1.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.92/1.49    inference(ennf_transformation,[],[f14])).
% 7.92/1.49  
% 7.92/1.49  fof(f19,plain,(
% 7.92/1.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f20,plain,(
% 7.92/1.49    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 7.92/1.49  
% 7.92/1.49  fof(f35,plain,(
% 7.92/1.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 7.92/1.49    inference(cnf_transformation,[],[f20])).
% 7.92/1.49  
% 7.92/1.49  fof(f45,plain,(
% 7.92/1.49    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 7.92/1.49    inference(definition_unfolding,[],[f35,f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f10,axiom,(
% 7.92/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f32,plain,(
% 7.92/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.92/1.49    inference(cnf_transformation,[],[f10])).
% 7.92/1.49  
% 7.92/1.49  fof(f5,axiom,(
% 7.92/1.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f27,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.92/1.49    inference(cnf_transformation,[],[f5])).
% 7.92/1.49  
% 7.92/1.49  fof(f12,axiom,(
% 7.92/1.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f34,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f12])).
% 7.92/1.49  
% 7.92/1.49  fof(f37,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.92/1.49    inference(definition_unfolding,[],[f34,f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f40,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 7.92/1.49    inference(definition_unfolding,[],[f27,f37])).
% 7.92/1.49  
% 7.92/1.49  fof(f8,axiom,(
% 7.92/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f30,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f8])).
% 7.92/1.49  
% 7.92/1.49  fof(f42,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 7.92/1.49    inference(definition_unfolding,[],[f30,f25,f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f7,axiom,(
% 7.92/1.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f29,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f7])).
% 7.92/1.49  
% 7.92/1.49  fof(f41,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 7.92/1.49    inference(definition_unfolding,[],[f29,f25,f37])).
% 7.92/1.49  
% 7.92/1.49  fof(f2,axiom,(
% 7.92/1.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.92/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f18,plain,(
% 7.92/1.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.92/1.49    inference(nnf_transformation,[],[f2])).
% 7.92/1.49  
% 7.92/1.49  fof(f24,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f18])).
% 7.92/1.49  
% 7.92/1.49  fof(f38,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 7.92/1.49    inference(definition_unfolding,[],[f24,f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f23,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f18])).
% 7.92/1.49  
% 7.92/1.49  fof(f39,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.92/1.49    inference(definition_unfolding,[],[f23,f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f36,plain,(
% 7.92/1.49    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f20])).
% 7.92/1.49  
% 7.92/1.49  fof(f22,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.92/1.49    inference(cnf_transformation,[],[f17])).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9,plain,
% 7.92/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.92/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1,plain,
% 7.92/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f21]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_80,plain,
% 7.92/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.92/1.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_11,plain,
% 7.92/1.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_141,plain,
% 7.92/1.49      ( X0 != X1
% 7.92/1.49      | k5_xboole_0(X2,k3_xboole_0(X2,X0)) != X3
% 7.92/1.49      | k3_xboole_0(X3,X1) = k1_xboole_0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_80,c_11]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_142,plain,
% 7.92/1.49      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_141]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_895,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X2)) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_9,c_142]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.92/1.49      inference(cnf_transformation,[],[f26]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1058,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X0,X2))) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_895,c_4]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_6,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_13,negated_conjecture,
% 7.92/1.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 7.92/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_202,plain,
% 7.92/1.49      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != X0
% 7.92/1.49      | k3_xboole_0(X1,X0) = X1
% 7.92/1.49      | sK0 != X1 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_203,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_202]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_447,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = k3_xboole_0(sK0,X0) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_203,c_4]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2495,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1))),k3_xboole_0(sK0,X1))) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_447,c_1058]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2874,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(sK0,k3_xboole_0(X0,sK2)))) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1058,c_2495]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_10,plain,
% 7.92/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2961,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X0,sK2)))) = k1_xboole_0 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_2874,c_10]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_501,plain,
% 7.92/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_4,c_9]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_18666,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,sK2)))) = k5_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_2961,c_501]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_8,plain,
% 7.92/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.92/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_285,plain,
% 7.92/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_8,c_4]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3475,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2))) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_5,c_285]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_461,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2)) = k3_xboole_0(X0,X2) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_503,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X2))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_5,c_9]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3687,plain,
% 7.92/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_3475,c_461,c_503]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_18963,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k3_xboole_0(sK0,X0) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_18666,c_10,c_3687]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1032,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK0)),k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_203,c_895]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7,plain,
% 7.92/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_283,plain,
% 7.92/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_7,c_5]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1084,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_1032,c_283]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1033,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1))) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_447,c_895]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1612,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k1_xboole_0) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1084,c_1033]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1644,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0),k5_xboole_0(sK0,sK0)),k1_xboole_0) = k1_xboole_0 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_1612,c_203]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1645,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_1644,c_283]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9280,plain,
% 7.92/1.49      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0),k1_xboole_0),k1_xboole_0)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1645,c_461]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1614,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_142,c_1033]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_538,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_447,c_4]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_678,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_4,c_538]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_688,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_678,c_447]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_903,plain,
% 7.92/1.49      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,X1))),X1) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_688,c_142]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_929,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_903,c_285,c_688]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_930,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_929,c_142]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_918,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_142,c_447]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_932,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_930,c_918]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1641,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_1614,c_932]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1642,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_1641,c_10]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2271,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k3_xboole_0(sK0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1642,c_4]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2311,plain,
% 7.92/1.49      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_447,c_2271]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2406,plain,
% 7.92/1.49      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0) = k1_xboole_0 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_2311,c_930]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_899,plain,
% 7.92/1.49      ( k3_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_203,c_142]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_936,plain,
% 7.92/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_899,c_283]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_535,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_5,c_447]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_543,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = sK0 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_535,c_203]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1598,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))),k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1)))) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_447,c_1033]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4662,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(sK0,sK0)),k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))))) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_543,c_1598]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_460,plain,
% 7.92/1.49      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,sK0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_203,c_5]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_84,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.92/1.49      inference(prop_impl,[status(thm)],[c_2]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_207,plain,
% 7.92/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 7.92/1.49      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != X1
% 7.92/1.49      | sK0 != X0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_84,c_13]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_208,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_207]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_282,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_208,c_203]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_466,plain,
% 7.92/1.49      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_460,c_282]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_467,plain,
% 7.92/1.49      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_466,c_10]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_507,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),sK0)) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_203,c_9]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_604,plain,
% 7.92/1.49      ( k5_xboole_0(k3_xboole_0(sK0,sK0),k3_xboole_0(k3_xboole_0(sK0,sK0),sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_203,c_507]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_610,plain,
% 7.92/1.49      ( k5_xboole_0(k3_xboole_0(sK0,sK0),k3_xboole_0(k3_xboole_0(sK0,sK0),sK0)) = k3_xboole_0(sK0,k1_xboole_0) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_604,c_283]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_677,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0))) = sK0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_610,c_5]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1005,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) = sK0 ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_677,c_677,c_930]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1006,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,sK0) = sK0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_1005,c_10]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3536,plain,
% 7.92/1.49      ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1006,c_285]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_504,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_203,c_9]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_618,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_5,c_504]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_626,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_618,c_543]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_627,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,k1_xboole_0) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_626,c_283]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3596,plain,
% 7.92/1.49      ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k3_xboole_0(sK0,k1_xboole_0)) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_3536,c_627]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3597,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_3596,c_283,c_930]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4780,plain,
% 7.92/1.49      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_4662,c_5,c_283,c_467,c_3597]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5402,plain,
% 7.92/1.49      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_936,c_4780]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9510,plain,
% 7.92/1.49      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_9280,c_2406,c_5402]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_679,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_5,c_538]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_740,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(sK0,X0) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_679,c_447]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_6919,plain,
% 7.92/1.49      ( k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0))),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k1_xboole_0))) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_2271,c_740]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_6961,plain,
% 7.92/1.49      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.92/1.49      inference(light_normalisation,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_6919,c_10,c_930,c_2406,c_3597]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7674,plain,
% 7.92/1.49      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),X1)) = k3_xboole_0(k1_xboole_0,X1) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_6961,c_4]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7680,plain,
% 7.92/1.49      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_6961,c_895]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9511,plain,
% 7.92/1.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_9510,c_10,c_7674,c_7680]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9694,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)),X1)) = k3_xboole_0(X0,X1) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_9511,c_461]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9763,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_9694,c_10]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_10115,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_9763,c_504]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19232,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_18963,c_10115]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19252,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK1) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_19232,c_18963]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19253,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_19252,c_932]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19254,plain,
% 7.92/1.49      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_19253,c_10]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3,plain,
% 7.92/1.49      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_82,plain,
% 7.92/1.49      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.92/1.49      inference(prop_impl,[status(thm)],[c_3]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_12,negated_conjecture,
% 7.92/1.49      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 7.92/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_157,plain,
% 7.92/1.49      ( ~ r1_tarski(sK0,sK1)
% 7.92/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK0
% 7.92/1.49      | sK2 != X1 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_12]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_158,plain,
% 7.92/1.49      ( ~ r1_tarski(sK0,sK1) | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0 ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_157]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_185,plain,
% 7.92/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 7.92/1.49      | k5_xboole_0(X2,k3_xboole_0(X2,sK2)) != sK0
% 7.92/1.49      | sK1 != X1
% 7.92/1.49      | sK0 != X0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_82,c_158]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_186,plain,
% 7.92/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0
% 7.92/1.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_185]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_448,plain,
% 7.92/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,sK2))) != sK0
% 7.92/1.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_4,c_186]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_451,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
% 7.92/1.49      | k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) != sK0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_448,c_285]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_0,plain,
% 7.92/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f22]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_78,plain,
% 7.92/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.92/1.49      inference(prop_impl,[status(thm)],[c_0]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_147,plain,
% 7.92/1.49      ( ~ r1_tarski(sK0,sK1)
% 7.92/1.49      | k3_xboole_0(X0,X1) != k1_xboole_0
% 7.92/1.49      | sK2 != X1
% 7.92/1.49      | sK0 != X0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_78,c_12]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_148,plain,
% 7.92/1.49      ( ~ r1_tarski(sK0,sK1) | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_147]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_194,plain,
% 7.92/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 7.92/1.49      | k3_xboole_0(sK0,sK2) != k1_xboole_0
% 7.92/1.49      | sK1 != X1
% 7.92/1.49      | sK0 != X0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_82,c_148]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_195,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
% 7.92/1.49      | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_194]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7485,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_451,c_195,c_932]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19496,plain,
% 7.92/1.49      ( k5_xboole_0(sK0,sK0) != k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_19254,c_7485]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19497,plain,
% 7.92/1.49      ( k1_xboole_0 != k1_xboole_0 ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_19496,c_283]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19498,plain,
% 7.92/1.49      ( $false ),
% 7.92/1.49      inference(equality_resolution_simp,[status(thm)],[c_19497]) ).
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  ------                               Statistics
% 7.92/1.49  
% 7.92/1.49  ------ General
% 7.92/1.49  
% 7.92/1.49  abstr_ref_over_cycles:                  0
% 7.92/1.49  abstr_ref_under_cycles:                 0
% 7.92/1.49  gc_basic_clause_elim:                   0
% 7.92/1.49  forced_gc_time:                         0
% 7.92/1.49  parsing_time:                           0.007
% 7.92/1.49  unif_index_cands_time:                  0.
% 7.92/1.49  unif_index_add_time:                    0.
% 7.92/1.49  orderings_time:                         0.
% 7.92/1.49  out_proof_time:                         0.008
% 7.92/1.49  total_time:                             0.797
% 7.92/1.49  num_of_symbols:                         41
% 7.92/1.49  num_of_terms:                           36365
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing
% 7.92/1.49  
% 7.92/1.49  num_of_splits:                          1
% 7.92/1.49  num_of_split_atoms:                     2
% 7.92/1.49  num_of_reused_defs:                     0
% 7.92/1.49  num_eq_ax_congr_red:                    0
% 7.92/1.49  num_of_sem_filtered_clauses:            0
% 7.92/1.49  num_of_subtypes:                        0
% 7.92/1.49  monotx_restored_types:                  0
% 7.92/1.49  sat_num_of_epr_types:                   0
% 7.92/1.49  sat_num_of_non_cyclic_types:            0
% 7.92/1.49  sat_guarded_non_collapsed_types:        0
% 7.92/1.49  num_pure_diseq_elim:                    0
% 7.92/1.49  simp_replaced_by:                       0
% 7.92/1.49  res_preprocessed:                       33
% 7.92/1.49  prep_upred:                             0
% 7.92/1.49  prep_unflattend:                        13
% 7.92/1.49  smt_new_axioms:                         0
% 7.92/1.49  pred_elim_cands:                        2
% 7.92/1.49  pred_elim:                              2
% 7.92/1.49  pred_elim_cl:                           0
% 7.92/1.49  pred_elim_cycles:                       3
% 7.92/1.49  merged_defs:                            4
% 7.92/1.49  merged_defs_ncl:                        0
% 7.92/1.49  bin_hyper_res:                          4
% 7.92/1.49  prep_cycles:                            2
% 7.92/1.49  pred_elim_time:                         0.002
% 7.92/1.49  splitting_time:                         0.
% 7.92/1.49  sem_filter_time:                        0.
% 7.92/1.49  monotx_time:                            0.
% 7.92/1.49  subtype_inf_time:                       0.
% 7.92/1.49  
% 7.92/1.49  ------ Problem properties
% 7.92/1.49  
% 7.92/1.49  clauses:                                15
% 7.92/1.49  conjectures:                            0
% 7.92/1.49  epr:                                    0
% 7.92/1.49  horn:                                   15
% 7.92/1.49  ground:                                 5
% 7.92/1.49  unary:                                  9
% 7.92/1.49  binary:                                 4
% 7.92/1.49  lits:                                   23
% 7.92/1.49  lits_eq:                                21
% 7.92/1.49  fd_pure:                                0
% 7.92/1.49  fd_pseudo:                              0
% 7.92/1.49  fd_cond:                                0
% 7.92/1.49  fd_pseudo_cond:                         0
% 7.92/1.49  ac_symbols:                             0
% 7.92/1.49  
% 7.92/1.49  ------ Propositional Solver
% 7.92/1.49  
% 7.92/1.49  prop_solver_calls:                      23
% 7.92/1.49  prop_fast_solver_calls:                 291
% 7.92/1.49  smt_solver_calls:                       0
% 7.92/1.49  smt_fast_solver_calls:                  0
% 7.92/1.49  prop_num_of_clauses:                    5364
% 7.92/1.49  prop_preprocess_simplified:             4185
% 7.92/1.49  prop_fo_subsumed:                       1
% 7.92/1.49  prop_solver_time:                       0.
% 7.92/1.49  smt_solver_time:                        0.
% 7.92/1.49  smt_fast_solver_time:                   0.
% 7.92/1.49  prop_fast_solver_time:                  0.
% 7.92/1.49  prop_unsat_core_time:                   0.
% 7.92/1.49  
% 7.92/1.49  ------ QBF
% 7.92/1.49  
% 7.92/1.49  qbf_q_res:                              0
% 7.92/1.49  qbf_num_tautologies:                    0
% 7.92/1.49  qbf_prep_cycles:                        0
% 7.92/1.49  
% 7.92/1.49  ------ BMC1
% 7.92/1.49  
% 7.92/1.49  bmc1_current_bound:                     -1
% 7.92/1.49  bmc1_last_solved_bound:                 -1
% 7.92/1.49  bmc1_unsat_core_size:                   -1
% 7.92/1.49  bmc1_unsat_core_parents_size:           -1
% 7.92/1.49  bmc1_merge_next_fun:                    0
% 7.92/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.92/1.49  
% 7.92/1.49  ------ Instantiation
% 7.92/1.49  
% 7.92/1.49  inst_num_of_clauses:                    1189
% 7.92/1.49  inst_num_in_passive:                    141
% 7.92/1.49  inst_num_in_active:                     519
% 7.92/1.49  inst_num_in_unprocessed:                531
% 7.92/1.49  inst_num_of_loops:                      590
% 7.92/1.49  inst_num_of_learning_restarts:          0
% 7.92/1.49  inst_num_moves_active_passive:          67
% 7.92/1.49  inst_lit_activity:                      0
% 7.92/1.49  inst_lit_activity_moves:                0
% 7.92/1.49  inst_num_tautologies:                   0
% 7.92/1.49  inst_num_prop_implied:                  0
% 7.92/1.49  inst_num_existing_simplified:           0
% 7.92/1.49  inst_num_eq_res_simplified:             0
% 7.92/1.49  inst_num_child_elim:                    0
% 7.92/1.49  inst_num_of_dismatching_blockings:      642
% 7.92/1.49  inst_num_of_non_proper_insts:           1446
% 7.92/1.49  inst_num_of_duplicates:                 0
% 7.92/1.49  inst_inst_num_from_inst_to_res:         0
% 7.92/1.49  inst_dismatching_checking_time:         0.
% 7.92/1.49  
% 7.92/1.49  ------ Resolution
% 7.92/1.49  
% 7.92/1.49  res_num_of_clauses:                     0
% 7.92/1.49  res_num_in_passive:                     0
% 7.92/1.49  res_num_in_active:                      0
% 7.92/1.49  res_num_of_loops:                       35
% 7.92/1.49  res_forward_subset_subsumed:            239
% 7.92/1.49  res_backward_subset_subsumed:           6
% 7.92/1.49  res_forward_subsumed:                   0
% 7.92/1.49  res_backward_subsumed:                  0
% 7.92/1.49  res_forward_subsumption_resolution:     0
% 7.92/1.49  res_backward_subsumption_resolution:    0
% 7.92/1.49  res_clause_to_clause_subsumption:       8431
% 7.92/1.49  res_orphan_elimination:                 0
% 7.92/1.49  res_tautology_del:                      175
% 7.92/1.49  res_num_eq_res_simplified:              2
% 7.92/1.49  res_num_sel_changes:                    0
% 7.92/1.49  res_moves_from_active_to_pass:          0
% 7.92/1.49  
% 7.92/1.49  ------ Superposition
% 7.92/1.49  
% 7.92/1.49  sup_time_total:                         0.
% 7.92/1.49  sup_time_generating:                    0.
% 7.92/1.49  sup_time_sim_full:                      0.
% 7.92/1.49  sup_time_sim_immed:                     0.
% 7.92/1.49  
% 7.92/1.49  sup_num_of_clauses:                     1716
% 7.92/1.49  sup_num_in_active:                      84
% 7.92/1.49  sup_num_in_passive:                     1632
% 7.92/1.49  sup_num_of_loops:                       116
% 7.92/1.49  sup_fw_superposition:                   3176
% 7.92/1.49  sup_bw_superposition:                   3257
% 7.92/1.49  sup_immediate_simplified:               4666
% 7.92/1.49  sup_given_eliminated:                   6
% 7.92/1.49  comparisons_done:                       0
% 7.92/1.49  comparisons_avoided:                    0
% 7.92/1.49  
% 7.92/1.49  ------ Simplifications
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  sim_fw_subset_subsumed:                 39
% 7.92/1.49  sim_bw_subset_subsumed:                 2
% 7.92/1.49  sim_fw_subsumed:                        251
% 7.92/1.49  sim_bw_subsumed:                        58
% 7.92/1.49  sim_fw_subsumption_res:                 0
% 7.92/1.49  sim_bw_subsumption_res:                 0
% 7.92/1.49  sim_tautology_del:                      61
% 7.92/1.49  sim_eq_tautology_del:                   2133
% 7.92/1.49  sim_eq_res_simp:                        3
% 7.92/1.49  sim_fw_demodulated:                     4066
% 7.92/1.49  sim_bw_demodulated:                     107
% 7.92/1.49  sim_light_normalised:                   1694
% 7.92/1.49  sim_joinable_taut:                      0
% 7.92/1.49  sim_joinable_simp:                      0
% 7.92/1.49  sim_ac_normalised:                      0
% 7.92/1.49  sim_smt_subsumption:                    0
% 7.92/1.49  
%------------------------------------------------------------------------------
