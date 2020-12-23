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
% DateTime   : Thu Dec  3 11:25:55 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  104 (1627 expanded)
%              Number of clauses        :   62 ( 558 expanded)
%              Number of leaves         :   14 ( 404 expanded)
%              Depth                    :   27
%              Number of atoms          :  154 (2723 expanded)
%              Number of equality atoms :  102 (1320 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f35,f25])).

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

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f32,f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f29,f25,f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

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

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

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

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_201,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != X0
    | k3_xboole_0(X1,X0) = X1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_202,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_445,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_202,c_4])).

cnf(c_517,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_445,c_4])).

cnf(c_739,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_4,c_517])).

cnf(c_753,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_739,c_445])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_79,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_140,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X0)) != X3
    | k3_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_79,c_10])).

cnf(c_141,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_140])).

cnf(c_907,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,X1))),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_753,c_141])).

cnf(c_7,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_283,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_7,c_4])).

cnf(c_929,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_907,c_283,c_753])).

cnf(c_930,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_929,c_141])).

cnf(c_919,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_141,c_445])).

cnf(c_932,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_930,c_919])).

cnf(c_8,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4091,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0)) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_932,c_8])).

cnf(c_4122,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) ),
    inference(demodulation,[status(thm)],[c_4091,c_283,c_753])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_740,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_5,c_517])).

cnf(c_780,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_740,c_445])).

cnf(c_1491,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_445,c_780])).

cnf(c_1773,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(k3_xboole_0(sK0,X1),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1),k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))))) = k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),k3_xboole_0(X0,k3_xboole_0(sK0,X1))) ),
    inference(superposition,[status(thm)],[c_1491,c_283])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1774,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1773,c_11,c_1491])).

cnf(c_4123,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k3_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_4122,c_9,c_1774])).

cnf(c_500,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_202,c_8])).

cnf(c_627,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_5,c_500])).

cnf(c_514,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_5,c_445])).

cnf(c_522,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_514,c_202])).

cnf(c_637,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_627,c_522])).

cnf(c_638,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_637,c_11])).

cnf(c_1001,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_638,c_638,c_930])).

cnf(c_1004,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1001,c_5])).

cnf(c_1005,plain,
    ( k3_xboole_0(sK0,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_1004,c_9])).

cnf(c_1015,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_1005,c_753])).

cnf(c_4768,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_1015,c_500])).

cnf(c_8055,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_4123,c_4768])).

cnf(c_8070,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_8055,c_4123])).

cnf(c_8071,plain,
    ( k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_8070,c_932])).

cnf(c_8072,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_8071,c_9])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_81,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_77,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_146,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_77,c_12])).

cnf(c_147,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_193,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | k3_xboole_0(sK0,sK2) != k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_81,c_147])).

cnf(c_194,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
    | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_4079,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_932,c_194])).

cnf(c_4080,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4079])).

cnf(c_8131,plain,
    ( k5_xboole_0(sK0,sK0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8072,c_4080])).

cnf(c_8132,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8131,c_11])).

cnf(c_8133,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8132])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:07:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.75/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/0.92  
% 3.75/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/0.92  
% 3.75/0.92  ------  iProver source info
% 3.75/0.92  
% 3.75/0.92  git: date: 2020-06-30 10:37:57 +0100
% 3.75/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/0.92  git: non_committed_changes: false
% 3.75/0.92  git: last_make_outside_of_git: false
% 3.75/0.92  
% 3.75/0.92  ------ 
% 3.75/0.92  
% 3.75/0.92  ------ Input Options
% 3.75/0.92  
% 3.75/0.92  --out_options                           all
% 3.75/0.92  --tptp_safe_out                         true
% 3.75/0.92  --problem_path                          ""
% 3.75/0.92  --include_path                          ""
% 3.75/0.92  --clausifier                            res/vclausify_rel
% 3.75/0.92  --clausifier_options                    ""
% 3.75/0.92  --stdin                                 false
% 3.75/0.92  --stats_out                             all
% 3.75/0.92  
% 3.75/0.92  ------ General Options
% 3.75/0.92  
% 3.75/0.92  --fof                                   false
% 3.75/0.92  --time_out_real                         305.
% 3.75/0.92  --time_out_virtual                      -1.
% 3.75/0.92  --symbol_type_check                     false
% 3.75/0.92  --clausify_out                          false
% 3.75/0.92  --sig_cnt_out                           false
% 4.06/0.92  --trig_cnt_out                          false
% 4.06/0.92  --trig_cnt_out_tolerance                1.
% 4.06/0.92  --trig_cnt_out_sk_spl                   false
% 4.06/0.92  --abstr_cl_out                          false
% 4.06/0.92  
% 4.06/0.92  ------ Global Options
% 4.06/0.92  
% 4.06/0.92  --schedule                              default
% 4.06/0.92  --add_important_lit                     false
% 4.06/0.92  --prop_solver_per_cl                    1000
% 4.06/0.92  --min_unsat_core                        false
% 4.06/0.92  --soft_assumptions                      false
% 4.06/0.92  --soft_lemma_size                       3
% 4.06/0.92  --prop_impl_unit_size                   0
% 4.06/0.92  --prop_impl_unit                        []
% 4.06/0.92  --share_sel_clauses                     true
% 4.06/0.92  --reset_solvers                         false
% 4.06/0.92  --bc_imp_inh                            [conj_cone]
% 4.06/0.92  --conj_cone_tolerance                   3.
% 4.06/0.92  --extra_neg_conj                        none
% 4.06/0.92  --large_theory_mode                     true
% 4.06/0.92  --prolific_symb_bound                   200
% 4.06/0.92  --lt_threshold                          2000
% 4.06/0.92  --clause_weak_htbl                      true
% 4.06/0.92  --gc_record_bc_elim                     false
% 4.06/0.92  
% 4.06/0.92  ------ Preprocessing Options
% 4.06/0.92  
% 4.06/0.92  --preprocessing_flag                    true
% 4.06/0.92  --time_out_prep_mult                    0.1
% 4.06/0.92  --splitting_mode                        input
% 4.06/0.92  --splitting_grd                         true
% 4.06/0.92  --splitting_cvd                         false
% 4.06/0.92  --splitting_cvd_svl                     false
% 4.06/0.92  --splitting_nvd                         32
% 4.06/0.92  --sub_typing                            true
% 4.06/0.92  --prep_gs_sim                           true
% 4.06/0.92  --prep_unflatten                        true
% 4.06/0.92  --prep_res_sim                          true
% 4.06/0.92  --prep_upred                            true
% 4.06/0.92  --prep_sem_filter                       exhaustive
% 4.06/0.92  --prep_sem_filter_out                   false
% 4.06/0.92  --pred_elim                             true
% 4.06/0.92  --res_sim_input                         true
% 4.06/0.92  --eq_ax_congr_red                       true
% 4.06/0.92  --pure_diseq_elim                       true
% 4.06/0.92  --brand_transform                       false
% 4.06/0.92  --non_eq_to_eq                          false
% 4.06/0.92  --prep_def_merge                        true
% 4.06/0.92  --prep_def_merge_prop_impl              false
% 4.06/0.92  --prep_def_merge_mbd                    true
% 4.06/0.92  --prep_def_merge_tr_red                 false
% 4.06/0.92  --prep_def_merge_tr_cl                  false
% 4.06/0.92  --smt_preprocessing                     true
% 4.06/0.92  --smt_ac_axioms                         fast
% 4.06/0.92  --preprocessed_out                      false
% 4.06/0.92  --preprocessed_stats                    false
% 4.06/0.92  
% 4.06/0.92  ------ Abstraction refinement Options
% 4.06/0.92  
% 4.06/0.92  --abstr_ref                             []
% 4.06/0.92  --abstr_ref_prep                        false
% 4.06/0.92  --abstr_ref_until_sat                   false
% 4.06/0.92  --abstr_ref_sig_restrict                funpre
% 4.06/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 4.06/0.92  --abstr_ref_under                       []
% 4.06/0.92  
% 4.06/0.92  ------ SAT Options
% 4.06/0.92  
% 4.06/0.92  --sat_mode                              false
% 4.06/0.92  --sat_fm_restart_options                ""
% 4.06/0.92  --sat_gr_def                            false
% 4.06/0.92  --sat_epr_types                         true
% 4.06/0.92  --sat_non_cyclic_types                  false
% 4.06/0.92  --sat_finite_models                     false
% 4.06/0.92  --sat_fm_lemmas                         false
% 4.06/0.92  --sat_fm_prep                           false
% 4.06/0.92  --sat_fm_uc_incr                        true
% 4.06/0.92  --sat_out_model                         small
% 4.06/0.92  --sat_out_clauses                       false
% 4.06/0.92  
% 4.06/0.92  ------ QBF Options
% 4.06/0.92  
% 4.06/0.92  --qbf_mode                              false
% 4.06/0.92  --qbf_elim_univ                         false
% 4.06/0.92  --qbf_dom_inst                          none
% 4.06/0.92  --qbf_dom_pre_inst                      false
% 4.06/0.92  --qbf_sk_in                             false
% 4.06/0.92  --qbf_pred_elim                         true
% 4.06/0.92  --qbf_split                             512
% 4.06/0.92  
% 4.06/0.92  ------ BMC1 Options
% 4.06/0.92  
% 4.06/0.92  --bmc1_incremental                      false
% 4.06/0.92  --bmc1_axioms                           reachable_all
% 4.06/0.92  --bmc1_min_bound                        0
% 4.06/0.92  --bmc1_max_bound                        -1
% 4.06/0.92  --bmc1_max_bound_default                -1
% 4.06/0.92  --bmc1_symbol_reachability              true
% 4.06/0.92  --bmc1_property_lemmas                  false
% 4.06/0.92  --bmc1_k_induction                      false
% 4.06/0.92  --bmc1_non_equiv_states                 false
% 4.06/0.92  --bmc1_deadlock                         false
% 4.06/0.92  --bmc1_ucm                              false
% 4.06/0.92  --bmc1_add_unsat_core                   none
% 4.06/0.92  --bmc1_unsat_core_children              false
% 4.06/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 4.06/0.92  --bmc1_out_stat                         full
% 4.06/0.92  --bmc1_ground_init                      false
% 4.06/0.92  --bmc1_pre_inst_next_state              false
% 4.06/0.92  --bmc1_pre_inst_state                   false
% 4.06/0.92  --bmc1_pre_inst_reach_state             false
% 4.06/0.92  --bmc1_out_unsat_core                   false
% 4.06/0.92  --bmc1_aig_witness_out                  false
% 4.06/0.92  --bmc1_verbose                          false
% 4.06/0.92  --bmc1_dump_clauses_tptp                false
% 4.06/0.92  --bmc1_dump_unsat_core_tptp             false
% 4.06/0.92  --bmc1_dump_file                        -
% 4.06/0.92  --bmc1_ucm_expand_uc_limit              128
% 4.06/0.92  --bmc1_ucm_n_expand_iterations          6
% 4.06/0.92  --bmc1_ucm_extend_mode                  1
% 4.06/0.92  --bmc1_ucm_init_mode                    2
% 4.06/0.92  --bmc1_ucm_cone_mode                    none
% 4.06/0.92  --bmc1_ucm_reduced_relation_type        0
% 4.06/0.92  --bmc1_ucm_relax_model                  4
% 4.06/0.92  --bmc1_ucm_full_tr_after_sat            true
% 4.06/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 4.06/0.92  --bmc1_ucm_layered_model                none
% 4.06/0.92  --bmc1_ucm_max_lemma_size               10
% 4.06/0.92  
% 4.06/0.92  ------ AIG Options
% 4.06/0.92  
% 4.06/0.92  --aig_mode                              false
% 4.06/0.92  
% 4.06/0.92  ------ Instantiation Options
% 4.06/0.92  
% 4.06/0.92  --instantiation_flag                    true
% 4.06/0.92  --inst_sos_flag                         true
% 4.06/0.92  --inst_sos_phase                        true
% 4.06/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.06/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.06/0.92  --inst_lit_sel_side                     num_symb
% 4.06/0.92  --inst_solver_per_active                1400
% 4.06/0.92  --inst_solver_calls_frac                1.
% 4.06/0.92  --inst_passive_queue_type               priority_queues
% 4.06/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.06/0.92  --inst_passive_queues_freq              [25;2]
% 4.06/0.92  --inst_dismatching                      true
% 4.06/0.92  --inst_eager_unprocessed_to_passive     true
% 4.06/0.92  --inst_prop_sim_given                   true
% 4.06/0.92  --inst_prop_sim_new                     false
% 4.06/0.92  --inst_subs_new                         false
% 4.06/0.92  --inst_eq_res_simp                      false
% 4.06/0.92  --inst_subs_given                       false
% 4.06/0.92  --inst_orphan_elimination               true
% 4.06/0.92  --inst_learning_loop_flag               true
% 4.06/0.92  --inst_learning_start                   3000
% 4.06/0.92  --inst_learning_factor                  2
% 4.06/0.92  --inst_start_prop_sim_after_learn       3
% 4.06/0.92  --inst_sel_renew                        solver
% 4.06/0.92  --inst_lit_activity_flag                true
% 4.06/0.92  --inst_restr_to_given                   false
% 4.06/0.92  --inst_activity_threshold               500
% 4.06/0.92  --inst_out_proof                        true
% 4.06/0.92  
% 4.06/0.92  ------ Resolution Options
% 4.06/0.92  
% 4.06/0.92  --resolution_flag                       true
% 4.06/0.92  --res_lit_sel                           adaptive
% 4.06/0.92  --res_lit_sel_side                      none
% 4.06/0.92  --res_ordering                          kbo
% 4.06/0.92  --res_to_prop_solver                    active
% 4.06/0.92  --res_prop_simpl_new                    false
% 4.06/0.92  --res_prop_simpl_given                  true
% 4.06/0.92  --res_passive_queue_type                priority_queues
% 4.06/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.06/0.92  --res_passive_queues_freq               [15;5]
% 4.06/0.92  --res_forward_subs                      full
% 4.06/0.92  --res_backward_subs                     full
% 4.06/0.92  --res_forward_subs_resolution           true
% 4.06/0.92  --res_backward_subs_resolution          true
% 4.06/0.92  --res_orphan_elimination                true
% 4.06/0.92  --res_time_limit                        2.
% 4.06/0.92  --res_out_proof                         true
% 4.06/0.92  
% 4.06/0.92  ------ Superposition Options
% 4.06/0.92  
% 4.06/0.92  --superposition_flag                    true
% 4.06/0.92  --sup_passive_queue_type                priority_queues
% 4.06/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.06/0.92  --sup_passive_queues_freq               [8;1;4]
% 4.06/0.92  --demod_completeness_check              fast
% 4.06/0.92  --demod_use_ground                      true
% 4.06/0.92  --sup_to_prop_solver                    passive
% 4.06/0.92  --sup_prop_simpl_new                    true
% 4.06/0.92  --sup_prop_simpl_given                  true
% 4.06/0.92  --sup_fun_splitting                     true
% 4.06/0.92  --sup_smt_interval                      50000
% 4.06/0.92  
% 4.06/0.92  ------ Superposition Simplification Setup
% 4.06/0.92  
% 4.06/0.92  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.06/0.92  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.06/0.92  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.06/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 4.06/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.06/0.92  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.06/0.92  --sup_immed_triv                        [TrivRules]
% 4.06/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.92  --sup_immed_bw_main                     []
% 4.06/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.06/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 4.06/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.92  --sup_input_bw                          []
% 4.06/0.92  
% 4.06/0.92  ------ Combination Options
% 4.06/0.92  
% 4.06/0.92  --comb_res_mult                         3
% 4.06/0.92  --comb_sup_mult                         2
% 4.06/0.92  --comb_inst_mult                        10
% 4.06/0.92  
% 4.06/0.92  ------ Debug Options
% 4.06/0.92  
% 4.06/0.92  --dbg_backtrace                         false
% 4.06/0.92  --dbg_dump_prop_clauses                 false
% 4.06/0.92  --dbg_dump_prop_clauses_file            -
% 4.06/0.92  --dbg_out_stat                          false
% 4.06/0.92  ------ Parsing...
% 4.06/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.06/0.92  
% 4.06/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 4.06/0.92  
% 4.06/0.92  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.06/0.92  
% 4.06/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.06/0.92  ------ Proving...
% 4.06/0.92  ------ Problem Properties 
% 4.06/0.92  
% 4.06/0.92  
% 4.06/0.92  clauses                                 15
% 4.06/0.92  conjectures                             0
% 4.06/0.92  EPR                                     0
% 4.06/0.92  Horn                                    15
% 4.06/0.92  unary                                   9
% 4.06/0.92  binary                                  4
% 4.06/0.92  lits                                    23
% 4.06/0.92  lits eq                                 21
% 4.06/0.92  fd_pure                                 0
% 4.06/0.92  fd_pseudo                               0
% 4.06/0.92  fd_cond                                 0
% 4.06/0.92  fd_pseudo_cond                          0
% 4.06/0.92  AC symbols                              0
% 4.06/0.92  
% 4.06/0.92  ------ Schedule dynamic 5 is on 
% 4.06/0.92  
% 4.06/0.92  ------ no conjectures: strip conj schedule 
% 4.06/0.92  
% 4.06/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 4.06/0.92  
% 4.06/0.92  
% 4.06/0.92  ------ 
% 4.06/0.92  Current options:
% 4.06/0.92  ------ 
% 4.06/0.92  
% 4.06/0.92  ------ Input Options
% 4.06/0.92  
% 4.06/0.92  --out_options                           all
% 4.06/0.92  --tptp_safe_out                         true
% 4.06/0.92  --problem_path                          ""
% 4.06/0.92  --include_path                          ""
% 4.06/0.92  --clausifier                            res/vclausify_rel
% 4.06/0.92  --clausifier_options                    ""
% 4.06/0.92  --stdin                                 false
% 4.06/0.92  --stats_out                             all
% 4.06/0.92  
% 4.06/0.92  ------ General Options
% 4.06/0.92  
% 4.06/0.92  --fof                                   false
% 4.06/0.92  --time_out_real                         305.
% 4.06/0.92  --time_out_virtual                      -1.
% 4.06/0.92  --symbol_type_check                     false
% 4.06/0.92  --clausify_out                          false
% 4.06/0.92  --sig_cnt_out                           false
% 4.06/0.92  --trig_cnt_out                          false
% 4.06/0.92  --trig_cnt_out_tolerance                1.
% 4.06/0.92  --trig_cnt_out_sk_spl                   false
% 4.06/0.92  --abstr_cl_out                          false
% 4.06/0.92  
% 4.06/0.92  ------ Global Options
% 4.06/0.92  
% 4.06/0.92  --schedule                              default
% 4.06/0.92  --add_important_lit                     false
% 4.06/0.92  --prop_solver_per_cl                    1000
% 4.06/0.92  --min_unsat_core                        false
% 4.06/0.92  --soft_assumptions                      false
% 4.06/0.92  --soft_lemma_size                       3
% 4.06/0.92  --prop_impl_unit_size                   0
% 4.06/0.92  --prop_impl_unit                        []
% 4.06/0.92  --share_sel_clauses                     true
% 4.06/0.92  --reset_solvers                         false
% 4.06/0.92  --bc_imp_inh                            [conj_cone]
% 4.06/0.92  --conj_cone_tolerance                   3.
% 4.06/0.92  --extra_neg_conj                        none
% 4.06/0.92  --large_theory_mode                     true
% 4.06/0.92  --prolific_symb_bound                   200
% 4.06/0.92  --lt_threshold                          2000
% 4.06/0.92  --clause_weak_htbl                      true
% 4.06/0.92  --gc_record_bc_elim                     false
% 4.06/0.92  
% 4.06/0.92  ------ Preprocessing Options
% 4.06/0.92  
% 4.06/0.92  --preprocessing_flag                    true
% 4.06/0.92  --time_out_prep_mult                    0.1
% 4.06/0.92  --splitting_mode                        input
% 4.06/0.92  --splitting_grd                         true
% 4.06/0.92  --splitting_cvd                         false
% 4.06/0.92  --splitting_cvd_svl                     false
% 4.06/0.92  --splitting_nvd                         32
% 4.06/0.92  --sub_typing                            true
% 4.06/0.92  --prep_gs_sim                           true
% 4.06/0.92  --prep_unflatten                        true
% 4.06/0.92  --prep_res_sim                          true
% 4.06/0.92  --prep_upred                            true
% 4.06/0.92  --prep_sem_filter                       exhaustive
% 4.06/0.92  --prep_sem_filter_out                   false
% 4.06/0.92  --pred_elim                             true
% 4.06/0.92  --res_sim_input                         true
% 4.06/0.92  --eq_ax_congr_red                       true
% 4.06/0.92  --pure_diseq_elim                       true
% 4.06/0.92  --brand_transform                       false
% 4.06/0.92  --non_eq_to_eq                          false
% 4.06/0.92  --prep_def_merge                        true
% 4.06/0.92  --prep_def_merge_prop_impl              false
% 4.06/0.92  --prep_def_merge_mbd                    true
% 4.06/0.92  --prep_def_merge_tr_red                 false
% 4.06/0.92  --prep_def_merge_tr_cl                  false
% 4.06/0.92  --smt_preprocessing                     true
% 4.06/0.92  --smt_ac_axioms                         fast
% 4.06/0.92  --preprocessed_out                      false
% 4.06/0.92  --preprocessed_stats                    false
% 4.06/0.92  
% 4.06/0.92  ------ Abstraction refinement Options
% 4.06/0.92  
% 4.06/0.92  --abstr_ref                             []
% 4.06/0.92  --abstr_ref_prep                        false
% 4.06/0.92  --abstr_ref_until_sat                   false
% 4.06/0.92  --abstr_ref_sig_restrict                funpre
% 4.06/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 4.06/0.92  --abstr_ref_under                       []
% 4.06/0.92  
% 4.06/0.92  ------ SAT Options
% 4.06/0.92  
% 4.06/0.92  --sat_mode                              false
% 4.06/0.92  --sat_fm_restart_options                ""
% 4.06/0.92  --sat_gr_def                            false
% 4.06/0.92  --sat_epr_types                         true
% 4.06/0.92  --sat_non_cyclic_types                  false
% 4.06/0.92  --sat_finite_models                     false
% 4.06/0.92  --sat_fm_lemmas                         false
% 4.06/0.92  --sat_fm_prep                           false
% 4.06/0.92  --sat_fm_uc_incr                        true
% 4.06/0.92  --sat_out_model                         small
% 4.06/0.92  --sat_out_clauses                       false
% 4.06/0.92  
% 4.06/0.92  ------ QBF Options
% 4.06/0.92  
% 4.06/0.92  --qbf_mode                              false
% 4.06/0.92  --qbf_elim_univ                         false
% 4.06/0.92  --qbf_dom_inst                          none
% 4.06/0.92  --qbf_dom_pre_inst                      false
% 4.06/0.92  --qbf_sk_in                             false
% 4.06/0.92  --qbf_pred_elim                         true
% 4.06/0.92  --qbf_split                             512
% 4.06/0.92  
% 4.06/0.92  ------ BMC1 Options
% 4.06/0.92  
% 4.06/0.92  --bmc1_incremental                      false
% 4.06/0.92  --bmc1_axioms                           reachable_all
% 4.06/0.92  --bmc1_min_bound                        0
% 4.06/0.92  --bmc1_max_bound                        -1
% 4.06/0.92  --bmc1_max_bound_default                -1
% 4.06/0.92  --bmc1_symbol_reachability              true
% 4.06/0.92  --bmc1_property_lemmas                  false
% 4.06/0.92  --bmc1_k_induction                      false
% 4.06/0.92  --bmc1_non_equiv_states                 false
% 4.06/0.92  --bmc1_deadlock                         false
% 4.06/0.92  --bmc1_ucm                              false
% 4.06/0.92  --bmc1_add_unsat_core                   none
% 4.06/0.92  --bmc1_unsat_core_children              false
% 4.06/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 4.06/0.92  --bmc1_out_stat                         full
% 4.06/0.92  --bmc1_ground_init                      false
% 4.06/0.92  --bmc1_pre_inst_next_state              false
% 4.06/0.92  --bmc1_pre_inst_state                   false
% 4.06/0.92  --bmc1_pre_inst_reach_state             false
% 4.06/0.92  --bmc1_out_unsat_core                   false
% 4.06/0.92  --bmc1_aig_witness_out                  false
% 4.06/0.92  --bmc1_verbose                          false
% 4.06/0.92  --bmc1_dump_clauses_tptp                false
% 4.06/0.92  --bmc1_dump_unsat_core_tptp             false
% 4.06/0.92  --bmc1_dump_file                        -
% 4.06/0.92  --bmc1_ucm_expand_uc_limit              128
% 4.06/0.92  --bmc1_ucm_n_expand_iterations          6
% 4.06/0.92  --bmc1_ucm_extend_mode                  1
% 4.06/0.92  --bmc1_ucm_init_mode                    2
% 4.06/0.92  --bmc1_ucm_cone_mode                    none
% 4.06/0.92  --bmc1_ucm_reduced_relation_type        0
% 4.06/0.92  --bmc1_ucm_relax_model                  4
% 4.06/0.92  --bmc1_ucm_full_tr_after_sat            true
% 4.06/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 4.06/0.92  --bmc1_ucm_layered_model                none
% 4.06/0.92  --bmc1_ucm_max_lemma_size               10
% 4.06/0.92  
% 4.06/0.92  ------ AIG Options
% 4.06/0.92  
% 4.06/0.92  --aig_mode                              false
% 4.06/0.92  
% 4.06/0.92  ------ Instantiation Options
% 4.06/0.92  
% 4.06/0.92  --instantiation_flag                    true
% 4.06/0.92  --inst_sos_flag                         true
% 4.06/0.92  --inst_sos_phase                        true
% 4.06/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.06/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.06/0.92  --inst_lit_sel_side                     none
% 4.06/0.92  --inst_solver_per_active                1400
% 4.06/0.92  --inst_solver_calls_frac                1.
% 4.06/0.92  --inst_passive_queue_type               priority_queues
% 4.06/0.92  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 4.06/0.92  --inst_passive_queues_freq              [25;2]
% 4.06/0.92  --inst_dismatching                      true
% 4.06/0.92  --inst_eager_unprocessed_to_passive     true
% 4.06/0.92  --inst_prop_sim_given                   true
% 4.06/0.92  --inst_prop_sim_new                     false
% 4.06/0.92  --inst_subs_new                         false
% 4.06/0.92  --inst_eq_res_simp                      false
% 4.06/0.92  --inst_subs_given                       false
% 4.06/0.92  --inst_orphan_elimination               true
% 4.06/0.92  --inst_learning_loop_flag               true
% 4.06/0.92  --inst_learning_start                   3000
% 4.06/0.92  --inst_learning_factor                  2
% 4.06/0.92  --inst_start_prop_sim_after_learn       3
% 4.06/0.92  --inst_sel_renew                        solver
% 4.06/0.92  --inst_lit_activity_flag                true
% 4.06/0.92  --inst_restr_to_given                   false
% 4.06/0.92  --inst_activity_threshold               500
% 4.06/0.92  --inst_out_proof                        true
% 4.06/0.92  
% 4.06/0.92  ------ Resolution Options
% 4.06/0.92  
% 4.06/0.92  --resolution_flag                       false
% 4.06/0.92  --res_lit_sel                           adaptive
% 4.06/0.92  --res_lit_sel_side                      none
% 4.06/0.92  --res_ordering                          kbo
% 4.06/0.92  --res_to_prop_solver                    active
% 4.06/0.92  --res_prop_simpl_new                    false
% 4.06/0.92  --res_prop_simpl_given                  true
% 4.06/0.92  --res_passive_queue_type                priority_queues
% 4.06/0.92  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 4.06/0.92  --res_passive_queues_freq               [15;5]
% 4.06/0.92  --res_forward_subs                      full
% 4.06/0.92  --res_backward_subs                     full
% 4.06/0.92  --res_forward_subs_resolution           true
% 4.06/0.92  --res_backward_subs_resolution          true
% 4.06/0.92  --res_orphan_elimination                true
% 4.06/0.92  --res_time_limit                        2.
% 4.06/0.92  --res_out_proof                         true
% 4.06/0.92  
% 4.06/0.92  ------ Superposition Options
% 4.06/0.92  
% 4.06/0.92  --superposition_flag                    true
% 4.06/0.92  --sup_passive_queue_type                priority_queues
% 4.06/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.06/0.92  --sup_passive_queues_freq               [8;1;4]
% 4.06/0.92  --demod_completeness_check              fast
% 4.06/0.92  --demod_use_ground                      true
% 4.06/0.92  --sup_to_prop_solver                    passive
% 4.06/0.92  --sup_prop_simpl_new                    true
% 4.06/0.92  --sup_prop_simpl_given                  true
% 4.06/0.92  --sup_fun_splitting                     true
% 4.06/0.92  --sup_smt_interval                      50000
% 4.06/0.92  
% 4.06/0.92  ------ Superposition Simplification Setup
% 4.06/0.92  
% 4.06/0.92  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.06/0.92  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.06/0.92  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.06/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.06/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 4.06/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.06/0.92  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.06/0.92  --sup_immed_triv                        [TrivRules]
% 4.06/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.92  --sup_immed_bw_main                     []
% 4.06/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.06/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 4.06/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.06/0.92  --sup_input_bw                          []
% 4.06/0.92  
% 4.06/0.92  ------ Combination Options
% 4.06/0.92  
% 4.06/0.92  --comb_res_mult                         3
% 4.06/0.92  --comb_sup_mult                         2
% 4.06/0.92  --comb_inst_mult                        10
% 4.06/0.92  
% 4.06/0.92  ------ Debug Options
% 4.06/0.92  
% 4.06/0.92  --dbg_backtrace                         false
% 4.06/0.92  --dbg_dump_prop_clauses                 false
% 4.06/0.92  --dbg_dump_prop_clauses_file            -
% 4.06/0.92  --dbg_out_stat                          false
% 4.06/0.92  
% 4.06/0.92  
% 4.06/0.92  
% 4.06/0.92  
% 4.06/0.92  ------ Proving...
% 4.06/0.92  
% 4.06/0.92  
% 4.06/0.92  % SZS status Theorem for theBenchmark.p
% 4.06/0.92  
% 4.06/0.92   Resolution empty clause
% 4.06/0.92  
% 4.06/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 4.06/0.92  
% 4.06/0.92  fof(f4,axiom,(
% 4.06/0.92    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f26,plain,(
% 4.06/0.92    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 4.06/0.92    inference(cnf_transformation,[],[f4])).
% 4.06/0.92  
% 4.06/0.92  fof(f6,axiom,(
% 4.06/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f15,plain,(
% 4.06/0.92    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.06/0.92    inference(ennf_transformation,[],[f6])).
% 4.06/0.92  
% 4.06/0.92  fof(f28,plain,(
% 4.06/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.06/0.92    inference(cnf_transformation,[],[f15])).
% 4.06/0.92  
% 4.06/0.92  fof(f13,conjecture,(
% 4.06/0.92    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f14,negated_conjecture,(
% 4.06/0.92    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 4.06/0.92    inference(negated_conjecture,[],[f13])).
% 4.06/0.92  
% 4.06/0.92  fof(f16,plain,(
% 4.06/0.92    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 4.06/0.92    inference(ennf_transformation,[],[f14])).
% 4.06/0.92  
% 4.06/0.92  fof(f19,plain,(
% 4.06/0.92    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 4.06/0.92    introduced(choice_axiom,[])).
% 4.06/0.92  
% 4.06/0.92  fof(f20,plain,(
% 4.06/0.92    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 4.06/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 4.06/0.92  
% 4.06/0.92  fof(f35,plain,(
% 4.06/0.92    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 4.06/0.92    inference(cnf_transformation,[],[f20])).
% 4.06/0.92  
% 4.06/0.92  fof(f3,axiom,(
% 4.06/0.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f25,plain,(
% 4.06/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.06/0.92    inference(cnf_transformation,[],[f3])).
% 4.06/0.92  
% 4.06/0.92  fof(f44,plain,(
% 4.06/0.92    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 4.06/0.92    inference(definition_unfolding,[],[f35,f25])).
% 4.06/0.92  
% 4.06/0.92  fof(f1,axiom,(
% 4.06/0.92    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f17,plain,(
% 4.06/0.92    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.06/0.92    inference(nnf_transformation,[],[f1])).
% 4.06/0.92  
% 4.06/0.92  fof(f21,plain,(
% 4.06/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.06/0.92    inference(cnf_transformation,[],[f17])).
% 4.06/0.92  
% 4.06/0.92  fof(f10,axiom,(
% 4.06/0.92    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f32,plain,(
% 4.06/0.92    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.06/0.92    inference(cnf_transformation,[],[f10])).
% 4.06/0.92  
% 4.06/0.92  fof(f43,plain,(
% 4.06/0.92    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 4.06/0.92    inference(definition_unfolding,[],[f32,f25])).
% 4.06/0.92  
% 4.06/0.92  fof(f7,axiom,(
% 4.06/0.92    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f29,plain,(
% 4.06/0.92    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 4.06/0.92    inference(cnf_transformation,[],[f7])).
% 4.06/0.92  
% 4.06/0.92  fof(f41,plain,(
% 4.06/0.92    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 4.06/0.92    inference(definition_unfolding,[],[f29,f25,f25])).
% 4.06/0.92  
% 4.06/0.92  fof(f8,axiom,(
% 4.06/0.92    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f30,plain,(
% 4.06/0.92    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 4.06/0.92    inference(cnf_transformation,[],[f8])).
% 4.06/0.92  
% 4.06/0.92  fof(f42,plain,(
% 4.06/0.92    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)))) )),
% 4.06/0.92    inference(definition_unfolding,[],[f30,f25,f25])).
% 4.06/0.92  
% 4.06/0.92  fof(f9,axiom,(
% 4.06/0.92    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f31,plain,(
% 4.06/0.92    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.06/0.92    inference(cnf_transformation,[],[f9])).
% 4.06/0.92  
% 4.06/0.92  fof(f5,axiom,(
% 4.06/0.92    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f27,plain,(
% 4.06/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 4.06/0.92    inference(cnf_transformation,[],[f5])).
% 4.06/0.92  
% 4.06/0.92  fof(f12,axiom,(
% 4.06/0.92    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f34,plain,(
% 4.06/0.92    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 4.06/0.92    inference(cnf_transformation,[],[f12])).
% 4.06/0.92  
% 4.06/0.92  fof(f37,plain,(
% 4.06/0.92    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 4.06/0.92    inference(definition_unfolding,[],[f34,f25])).
% 4.06/0.92  
% 4.06/0.92  fof(f40,plain,(
% 4.06/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 4.06/0.92    inference(definition_unfolding,[],[f27,f37])).
% 4.06/0.92  
% 4.06/0.92  fof(f11,axiom,(
% 4.06/0.92    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f33,plain,(
% 4.06/0.92    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.06/0.92    inference(cnf_transformation,[],[f11])).
% 4.06/0.92  
% 4.06/0.92  fof(f2,axiom,(
% 4.06/0.92    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 4.06/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.06/0.92  
% 4.06/0.92  fof(f18,plain,(
% 4.06/0.92    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 4.06/0.92    inference(nnf_transformation,[],[f2])).
% 4.06/0.92  
% 4.06/0.92  fof(f23,plain,(
% 4.06/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 4.06/0.92    inference(cnf_transformation,[],[f18])).
% 4.06/0.92  
% 4.06/0.92  fof(f39,plain,(
% 4.06/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.06/0.92    inference(definition_unfolding,[],[f23,f25])).
% 4.06/0.92  
% 4.06/0.92  fof(f22,plain,(
% 4.06/0.92    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.06/0.92    inference(cnf_transformation,[],[f17])).
% 4.06/0.92  
% 4.06/0.92  fof(f36,plain,(
% 4.06/0.92    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 4.06/0.92    inference(cnf_transformation,[],[f20])).
% 4.06/0.92  
% 4.06/0.92  cnf(c_4,plain,
% 4.06/0.92      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 4.06/0.92      inference(cnf_transformation,[],[f26]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_6,plain,
% 4.06/0.92      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 4.06/0.92      inference(cnf_transformation,[],[f28]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_13,negated_conjecture,
% 4.06/0.92      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 4.06/0.92      inference(cnf_transformation,[],[f44]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_201,plain,
% 4.06/0.92      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != X0
% 4.06/0.92      | k3_xboole_0(X1,X0) = X1
% 4.06/0.92      | sK0 != X1 ),
% 4.06/0.92      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_202,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
% 4.06/0.92      inference(unflattening,[status(thm)],[c_201]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_445,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = k3_xboole_0(sK0,X0) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_202,c_4]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_517,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_445,c_4]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_739,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_4,c_517]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_753,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_739,c_445]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_1,plain,
% 4.06/0.92      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 4.06/0.92      inference(cnf_transformation,[],[f21]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_79,plain,
% 4.06/0.92      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 4.06/0.92      inference(prop_impl,[status(thm)],[c_1]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_10,plain,
% 4.06/0.92      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 4.06/0.92      inference(cnf_transformation,[],[f43]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_140,plain,
% 4.06/0.92      ( X0 != X1
% 4.06/0.92      | k5_xboole_0(X2,k3_xboole_0(X2,X0)) != X3
% 4.06/0.92      | k3_xboole_0(X3,X1) = k1_xboole_0 ),
% 4.06/0.92      inference(resolution_lifted,[status(thm)],[c_79,c_10]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_141,plain,
% 4.06/0.92      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 4.06/0.92      inference(unflattening,[status(thm)],[c_140]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_907,plain,
% 4.06/0.92      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,X1))),X1) = k1_xboole_0 ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_753,c_141]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_7,plain,
% 4.06/0.92      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 4.06/0.92      inference(cnf_transformation,[],[f41]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_283,plain,
% 4.06/0.92      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 4.06/0.92      inference(light_normalisation,[status(thm)],[c_7,c_4]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_929,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k1_xboole_0 ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_907,c_283,c_753]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_930,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
% 4.06/0.92      inference(light_normalisation,[status(thm)],[c_929,c_141]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_919,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK2) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_141,c_445]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_932,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_930,c_919]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_8,plain,
% 4.06/0.92      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 4.06/0.92      inference(cnf_transformation,[],[f42]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_4091,plain,
% 4.06/0.92      ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0)) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_932,c_8]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_4122,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_4091,c_283,c_753]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_9,plain,
% 4.06/0.92      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.06/0.92      inference(cnf_transformation,[],[f31]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_5,plain,
% 4.06/0.92      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 4.06/0.92      inference(cnf_transformation,[],[f40]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_740,plain,
% 4.06/0.92      ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_5,c_517]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_780,plain,
% 4.06/0.92      ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k3_xboole_0(sK0,X0) ),
% 4.06/0.92      inference(light_normalisation,[status(thm)],[c_740,c_445]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_1491,plain,
% 4.06/0.92      ( k3_xboole_0(k3_xboole_0(sK0,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) = k3_xboole_0(sK0,X0) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_445,c_780]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_1773,plain,
% 4.06/0.92      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(k3_xboole_0(sK0,X1),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1),k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))))) = k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK0,X1)),k3_xboole_0(X0,k3_xboole_0(sK0,X1))) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_1491,c_283]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_11,plain,
% 4.06/0.92      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.06/0.92      inference(cnf_transformation,[],[f33]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_1774,plain,
% 4.06/0.92      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_1773,c_11,c_1491]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_4123,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK2))) = k3_xboole_0(sK0,X0) ),
% 4.06/0.92      inference(light_normalisation,[status(thm)],[c_4122,c_9,c_1774]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_500,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_202,c_8]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_627,plain,
% 4.06/0.92      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_5,c_500]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_514,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_5,c_445]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_522,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = sK0 ),
% 4.06/0.92      inference(light_normalisation,[status(thm)],[c_514,c_202]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_637,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) ),
% 4.06/0.92      inference(light_normalisation,[status(thm)],[c_627,c_522]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_638,plain,
% 4.06/0.92      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,k1_xboole_0) ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_637,c_11]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_1001,plain,
% 4.06/0.92      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) = k1_xboole_0 ),
% 4.06/0.92      inference(light_normalisation,[status(thm)],[c_638,c_638,c_930]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_1004,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) = sK0 ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_1001,c_5]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_1005,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,sK0) = sK0 ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_1004,c_9]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_1015,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_1005,c_753]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_4768,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_1015,c_500]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_8055,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
% 4.06/0.92      inference(superposition,[status(thm)],[c_4123,c_4768]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_8070,plain,
% 4.06/0.92      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK1) ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_8055,c_4123]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_8071,plain,
% 4.06/0.92      ( k5_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,sK1) ),
% 4.06/0.92      inference(light_normalisation,[status(thm)],[c_8070,c_932]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_8072,plain,
% 4.06/0.92      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_8071,c_9]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_3,plain,
% 4.06/0.92      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 4.06/0.92      inference(cnf_transformation,[],[f39]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_81,plain,
% 4.06/0.92      ( r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 4.06/0.92      inference(prop_impl,[status(thm)],[c_3]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_0,plain,
% 4.06/0.92      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 4.06/0.92      inference(cnf_transformation,[],[f22]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_77,plain,
% 4.06/0.92      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 4.06/0.92      inference(prop_impl,[status(thm)],[c_0]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_12,negated_conjecture,
% 4.06/0.92      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 4.06/0.92      inference(cnf_transformation,[],[f36]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_146,plain,
% 4.06/0.92      ( ~ r1_tarski(sK0,sK1)
% 4.06/0.92      | k3_xboole_0(X0,X1) != k1_xboole_0
% 4.06/0.92      | sK2 != X1
% 4.06/0.92      | sK0 != X0 ),
% 4.06/0.92      inference(resolution_lifted,[status(thm)],[c_77,c_12]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_147,plain,
% 4.06/0.92      ( ~ r1_tarski(sK0,sK1) | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 4.06/0.92      inference(unflattening,[status(thm)],[c_146]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_193,plain,
% 4.06/0.92      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 4.06/0.92      | k3_xboole_0(sK0,sK2) != k1_xboole_0
% 4.06/0.92      | sK1 != X1
% 4.06/0.92      | sK0 != X0 ),
% 4.06/0.92      inference(resolution_lifted,[status(thm)],[c_81,c_147]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_194,plain,
% 4.06/0.92      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
% 4.06/0.92      | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 4.06/0.92      inference(unflattening,[status(thm)],[c_193]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_4079,plain,
% 4.06/0.92      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
% 4.06/0.92      | k1_xboole_0 != k1_xboole_0 ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_932,c_194]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_4080,plain,
% 4.06/0.92      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 4.06/0.92      inference(equality_resolution_simp,[status(thm)],[c_4079]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_8131,plain,
% 4.06/0.92      ( k5_xboole_0(sK0,sK0) != k1_xboole_0 ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_8072,c_4080]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_8132,plain,
% 4.06/0.92      ( k1_xboole_0 != k1_xboole_0 ),
% 4.06/0.92      inference(demodulation,[status(thm)],[c_8131,c_11]) ).
% 4.06/0.92  
% 4.06/0.92  cnf(c_8133,plain,
% 4.06/0.92      ( $false ),
% 4.06/0.92      inference(equality_resolution_simp,[status(thm)],[c_8132]) ).
% 4.06/0.92  
% 4.06/0.92  
% 4.06/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 4.06/0.92  
% 4.06/0.92  ------                               Statistics
% 4.06/0.92  
% 4.06/0.92  ------ General
% 4.06/0.92  
% 4.06/0.92  abstr_ref_over_cycles:                  0
% 4.06/0.92  abstr_ref_under_cycles:                 0
% 4.06/0.92  gc_basic_clause_elim:                   0
% 4.06/0.92  forced_gc_time:                         0
% 4.06/0.92  parsing_time:                           0.005
% 4.06/0.92  unif_index_cands_time:                  0.
% 4.06/0.92  unif_index_add_time:                    0.
% 4.06/0.92  orderings_time:                         0.
% 4.06/0.92  out_proof_time:                         0.009
% 4.06/0.92  total_time:                             0.408
% 4.06/0.92  num_of_symbols:                         40
% 4.06/0.92  num_of_terms:                           14253
% 4.06/0.92  
% 4.06/0.92  ------ Preprocessing
% 4.06/0.92  
% 4.06/0.92  num_of_splits:                          1
% 4.06/0.92  num_of_split_atoms:                     1
% 4.06/0.92  num_of_reused_defs:                     0
% 4.06/0.92  num_eq_ax_congr_red:                    0
% 4.06/0.92  num_of_sem_filtered_clauses:            0
% 4.06/0.92  num_of_subtypes:                        0
% 4.06/0.92  monotx_restored_types:                  0
% 4.06/0.92  sat_num_of_epr_types:                   0
% 4.06/0.92  sat_num_of_non_cyclic_types:            0
% 4.06/0.92  sat_guarded_non_collapsed_types:        0
% 4.06/0.92  num_pure_diseq_elim:                    0
% 4.06/0.92  simp_replaced_by:                       0
% 4.06/0.92  res_preprocessed:                       33
% 4.06/0.92  prep_upred:                             0
% 4.06/0.92  prep_unflattend:                        13
% 4.06/0.92  smt_new_axioms:                         0
% 4.06/0.92  pred_elim_cands:                        2
% 4.06/0.92  pred_elim:                              2
% 4.06/0.92  pred_elim_cl:                           0
% 4.06/0.92  pred_elim_cycles:                       3
% 4.06/0.92  merged_defs:                            4
% 4.06/0.92  merged_defs_ncl:                        0
% 4.06/0.92  bin_hyper_res:                          4
% 4.06/0.92  prep_cycles:                            2
% 4.06/0.92  pred_elim_time:                         0.001
% 4.06/0.92  splitting_time:                         0.
% 4.06/0.92  sem_filter_time:                        0.
% 4.06/0.92  monotx_time:                            0.
% 4.06/0.92  subtype_inf_time:                       0.
% 4.06/0.92  
% 4.06/0.92  ------ Problem properties
% 4.06/0.92  
% 4.06/0.92  clauses:                                15
% 4.06/0.92  conjectures:                            0
% 4.06/0.92  epr:                                    0
% 4.06/0.92  horn:                                   15
% 4.06/0.92  ground:                                 5
% 4.06/0.92  unary:                                  9
% 4.06/0.92  binary:                                 4
% 4.06/0.92  lits:                                   23
% 4.06/0.92  lits_eq:                                21
% 4.06/0.92  fd_pure:                                0
% 4.06/0.92  fd_pseudo:                              0
% 4.06/0.92  fd_cond:                                0
% 4.06/0.92  fd_pseudo_cond:                         0
% 4.06/0.92  ac_symbols:                             0
% 4.06/0.92  
% 4.06/0.92  ------ Propositional Solver
% 4.06/0.92  
% 4.06/0.92  prop_solver_calls:                      23
% 4.06/0.92  prop_fast_solver_calls:                 239
% 4.06/0.92  smt_solver_calls:                       0
% 4.06/0.92  smt_fast_solver_calls:                  0
% 4.06/0.92  prop_num_of_clauses:                    2535
% 4.06/0.92  prop_preprocess_simplified:             3162
% 4.06/0.92  prop_fo_subsumed:                       2
% 4.06/0.92  prop_solver_time:                       0.
% 4.06/0.92  smt_solver_time:                        0.
% 4.06/0.92  smt_fast_solver_time:                   0.
% 4.06/0.92  prop_fast_solver_time:                  0.
% 4.06/0.92  prop_unsat_core_time:                   0.
% 4.06/0.92  
% 4.06/0.92  ------ QBF
% 4.06/0.92  
% 4.06/0.92  qbf_q_res:                              0
% 4.06/0.92  qbf_num_tautologies:                    0
% 4.06/0.92  qbf_prep_cycles:                        0
% 4.06/0.92  
% 4.06/0.92  ------ BMC1
% 4.06/0.92  
% 4.06/0.92  bmc1_current_bound:                     -1
% 4.06/0.92  bmc1_last_solved_bound:                 -1
% 4.06/0.92  bmc1_unsat_core_size:                   -1
% 4.06/0.92  bmc1_unsat_core_parents_size:           -1
% 4.06/0.92  bmc1_merge_next_fun:                    0
% 4.06/0.92  bmc1_unsat_core_clauses_time:           0.
% 4.06/0.92  
% 4.06/0.92  ------ Instantiation
% 4.06/0.92  
% 4.06/0.92  inst_num_of_clauses:                    743
% 4.06/0.92  inst_num_in_passive:                    312
% 4.06/0.92  inst_num_in_active:                     347
% 4.06/0.92  inst_num_in_unprocessed:                85
% 4.06/0.92  inst_num_of_loops:                      410
% 4.06/0.92  inst_num_of_learning_restarts:          0
% 4.06/0.92  inst_num_moves_active_passive:          59
% 4.06/0.92  inst_lit_activity:                      0
% 4.06/0.92  inst_lit_activity_moves:                0
% 4.06/0.92  inst_num_tautologies:                   0
% 4.06/0.92  inst_num_prop_implied:                  0
% 4.06/0.92  inst_num_existing_simplified:           0
% 4.06/0.92  inst_num_eq_res_simplified:             0
% 4.06/0.92  inst_num_child_elim:                    0
% 4.06/0.92  inst_num_of_dismatching_blockings:      283
% 4.06/0.92  inst_num_of_non_proper_insts:           860
% 4.06/0.92  inst_num_of_duplicates:                 0
% 4.06/0.92  inst_inst_num_from_inst_to_res:         0
% 4.06/0.92  inst_dismatching_checking_time:         0.
% 4.06/0.92  
% 4.06/0.92  ------ Resolution
% 4.06/0.92  
% 4.06/0.92  res_num_of_clauses:                     0
% 4.06/0.92  res_num_in_passive:                     0
% 4.06/0.92  res_num_in_active:                      0
% 4.06/0.92  res_num_of_loops:                       35
% 4.06/0.92  res_forward_subset_subsumed:            129
% 4.06/0.92  res_backward_subset_subsumed:           2
% 4.06/0.92  res_forward_subsumed:                   0
% 4.06/0.92  res_backward_subsumed:                  0
% 4.06/0.92  res_forward_subsumption_resolution:     0
% 4.06/0.92  res_backward_subsumption_resolution:    0
% 4.06/0.92  res_clause_to_clause_subsumption:       2516
% 4.06/0.92  res_orphan_elimination:                 0
% 4.06/0.92  res_tautology_del:                      96
% 4.06/0.92  res_num_eq_res_simplified:              2
% 4.06/0.92  res_num_sel_changes:                    0
% 4.06/0.92  res_moves_from_active_to_pass:          0
% 4.06/0.92  
% 4.06/0.92  ------ Superposition
% 4.06/0.92  
% 4.06/0.92  sup_time_total:                         0.
% 4.06/0.92  sup_time_generating:                    0.
% 4.06/0.92  sup_time_sim_full:                      0.
% 4.06/0.92  sup_time_sim_immed:                     0.
% 4.06/0.92  
% 4.06/0.92  sup_num_of_clauses:                     661
% 4.06/0.92  sup_num_in_active:                      60
% 4.06/0.92  sup_num_in_passive:                     601
% 4.06/0.92  sup_num_of_loops:                       81
% 4.06/0.92  sup_fw_superposition:                   1005
% 4.06/0.92  sup_bw_superposition:                   1161
% 4.06/0.92  sup_immediate_simplified:               1736
% 4.06/0.92  sup_given_eliminated:                   5
% 4.06/0.92  comparisons_done:                       0
% 4.06/0.92  comparisons_avoided:                    0
% 4.06/0.92  
% 4.06/0.92  ------ Simplifications
% 4.06/0.92  
% 4.06/0.92  
% 4.06/0.92  sim_fw_subset_subsumed:                 36
% 4.06/0.92  sim_bw_subset_subsumed:                 3
% 4.06/0.92  sim_fw_subsumed:                        128
% 4.06/0.92  sim_bw_subsumed:                        18
% 4.06/0.92  sim_fw_subsumption_res:                 0
% 4.06/0.92  sim_bw_subsumption_res:                 0
% 4.06/0.92  sim_tautology_del:                      15
% 4.06/0.92  sim_eq_tautology_del:                   635
% 4.06/0.92  sim_eq_res_simp:                        5
% 4.06/0.92  sim_fw_demodulated:                     1285
% 4.06/0.92  sim_bw_demodulated:                     43
% 4.06/0.92  sim_light_normalised:                   710
% 4.06/0.92  sim_joinable_taut:                      0
% 4.06/0.92  sim_joinable_simp:                      0
% 4.06/0.92  sim_ac_normalised:                      0
% 4.06/0.92  sim_smt_subsumption:                    0
% 4.06/0.92  
%------------------------------------------------------------------------------
