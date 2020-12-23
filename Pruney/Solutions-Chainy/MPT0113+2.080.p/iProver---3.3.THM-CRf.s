%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:55 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  158 (16510 expanded)
%              Number of clauses        :  118 (5258 expanded)
%              Number of leaves         :   13 (4345 expanded)
%              Depth                    :   33
%              Number of atoms          :  209 (25617 expanded)
%              Number of equality atoms :  151 (13156 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   11 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f26])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21])).

fof(f35,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f35,f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f31,f26,f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f32,f26,f26,f26])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_385,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_717,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_385])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_382,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_384,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1120,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_382,c_384])).

cnf(c_1319,plain,
    ( r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_717,c_1120])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_383,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1377,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1319,c_383])).

cnf(c_561,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_382,c_383])).

cnf(c_562,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_561,c_3])).

cnf(c_7,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_387,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_7,c_3])).

cnf(c_1288,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_562,c_387])).

cnf(c_1302,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1288,c_561])).

cnf(c_8,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_670,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1))))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_562,c_8])).

cnf(c_1401,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) ),
    inference(superposition,[status(thm)],[c_1302,c_670])).

cnf(c_1402,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_1401,c_561,c_562])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1403,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_1402,c_10])).

cnf(c_1653,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_1377,c_1403])).

cnf(c_1654,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1653,c_1377])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1655,plain,
    ( k2_xboole_0(k1_xboole_0,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_1654,c_9,c_10])).

cnf(c_650,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_1291,plain,
    ( k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_561,c_387])).

cnf(c_1298,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k5_xboole_0(sK0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_1291,c_561])).

cnf(c_1299,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1298,c_10])).

cnf(c_1759,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_650,c_9,c_650,c_1299])).

cnf(c_1909,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(X0,sK0)) = X0 ),
    inference(superposition,[status(thm)],[c_1655,c_1759])).

cnf(c_1910,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,sK0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1909,c_9,c_1299])).

cnf(c_3267,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_1910])).

cnf(c_654,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))) = k2_xboole_0(k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)),k3_xboole_0(X0,X3)) ),
    inference(superposition,[status(thm)],[c_8,c_8])).

cnf(c_4216,plain,
    ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_1302,c_654])).

cnf(c_1783,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_1759,c_1377])).

cnf(c_4343,plain,
    ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4216,c_1403,c_1783])).

cnf(c_1652,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1299,c_1403])).

cnf(c_1656,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1652,c_9,c_10,c_1299])).

cnf(c_2050,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_1656,c_1759])).

cnf(c_2051,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2050,c_9,c_1299])).

cnf(c_2053,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2051,c_6])).

cnf(c_3285,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_2053,c_1759])).

cnf(c_737,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_717,c_383])).

cnf(c_3318,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3285,c_737])).

cnf(c_4344,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_4343,c_10,c_3318])).

cnf(c_20874,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK2,sK0)) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_3267,c_4344])).

cnf(c_12887,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k2_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_1302,c_4344])).

cnf(c_12916,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_12887,c_1302])).

cnf(c_13957,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12916,c_6])).

cnf(c_669,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_562,c_3])).

cnf(c_823,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_3,c_669])).

cnf(c_827,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_823,c_562])).

cnf(c_648,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) ),
    inference(superposition,[status(thm)],[c_561,c_8])).

cnf(c_4296,plain,
    ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,X1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),sK0) ),
    inference(superposition,[status(thm)],[c_654,c_648])).

cnf(c_4305,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),sK0) = k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,X1)),sK0) ),
    inference(light_normalisation,[status(thm)],[c_4296,c_561])).

cnf(c_1762,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_1759])).

cnf(c_6297,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_4305,c_1762])).

cnf(c_9258,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)))),sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) ),
    inference(superposition,[status(thm)],[c_562,c_6297])).

cnf(c_9337,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)))),sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9258,c_562])).

cnf(c_1287,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_3,c_387])).

cnf(c_1303,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(light_normalisation,[status(thm)],[c_1287,c_3])).

cnf(c_1290,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) ),
    inference(superposition,[status(thm)],[c_3,c_387])).

cnf(c_1304,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_1303,c_1290])).

cnf(c_652,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X3)) ),
    inference(superposition,[status(thm)],[c_3,c_8])).

cnf(c_656,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X3)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
    inference(demodulation,[status(thm)],[c_652,c_387])).

cnf(c_7821,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
    inference(superposition,[status(thm)],[c_656,c_8])).

cnf(c_7893,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
    inference(light_normalisation,[status(thm)],[c_7821,c_1304])).

cnf(c_9338,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))),sK0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_9337,c_1304,c_3318,c_7893])).

cnf(c_9339,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),sK0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(demodulation,[status(thm)],[c_9338,c_562])).

cnf(c_9577,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))))),sK0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) ),
    inference(superposition,[status(thm)],[c_9339,c_9339])).

cnf(c_3287,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2053,c_8])).

cnf(c_3319,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3318,c_3287])).

cnf(c_1768,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1))) = sK0 ),
    inference(superposition,[status(thm)],[c_562,c_1759])).

cnf(c_2363,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)),X1))) = sK0 ),
    inference(superposition,[status(thm)],[c_562,c_1768])).

cnf(c_3987,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),X0))) = sK0 ),
    inference(superposition,[status(thm)],[c_561,c_2363])).

cnf(c_4007,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),X0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_3987,c_10,c_3318])).

cnf(c_1764,plain,
    ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0),k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),X1))) = sK0 ),
    inference(superposition,[status(thm)],[c_648,c_1759])).

cnf(c_3723,plain,
    ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0),k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK0,sK0),X0))) = sK0 ),
    inference(superposition,[status(thm)],[c_561,c_1764])).

cnf(c_777,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_561,c_648])).

cnf(c_781,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_777,c_10])).

cnf(c_1500,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1299,c_781])).

cnf(c_1501,plain,
    ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_1500,c_9])).

cnf(c_3729,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK0,sK0),X0))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3723,c_1501])).

cnf(c_3730,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK0,X0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_3729,c_10,c_3318])).

cnf(c_4457,plain,
    ( k2_xboole_0(sK0,sK0) = sK0 ),
    inference(superposition,[status(thm)],[c_4007,c_3730])).

cnf(c_9640,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_9577,c_9,c_10,c_827,c_1299,c_3319,c_4457])).

cnf(c_10670,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
    inference(superposition,[status(thm)],[c_9640,c_387])).

cnf(c_10751,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10670,c_10])).

cnf(c_649,plain,
    ( k2_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)),k3_xboole_0(k3_xboole_0(X0,X1),X3)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
    inference(superposition,[status(thm)],[c_3,c_8])).

cnf(c_657,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(k3_xboole_0(X0,X1),X3)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
    inference(light_normalisation,[status(thm)],[c_649,c_3,c_387])).

cnf(c_11016,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_10751,c_657])).

cnf(c_11082,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_11016,c_827])).

cnf(c_1651,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) ),
    inference(superposition,[status(thm)],[c_1302,c_1403])).

cnf(c_1657,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) = k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ),
    inference(demodulation,[status(thm)],[c_1651,c_1403])).

cnf(c_1658,plain,
    ( k2_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_1657,c_1302])).

cnf(c_1734,plain,
    ( k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k2_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) ),
    inference(superposition,[status(thm)],[c_1302,c_1658])).

cnf(c_1742,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_1734,c_1302,c_1403,c_1658])).

cnf(c_10695,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)))) ),
    inference(superposition,[status(thm)],[c_9640,c_1742])).

cnf(c_10733,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ),
    inference(demodulation,[status(thm)],[c_10695,c_9640])).

cnf(c_10734,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_10733,c_1403,c_3318])).

cnf(c_11083,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_11082,c_387,c_10734])).

cnf(c_13960,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13957,c_827,c_11083])).

cnf(c_20875,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20874,c_13960])).

cnf(c_1374,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1319])).

cnf(c_1629,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1374])).

cnf(c_1637,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1629,c_9,c_1299])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_119,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_120,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_119])).

cnf(c_121,plain,
    ( k3_xboole_0(sK0,sK2) != k1_xboole_0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_120])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20875,c_1637,c_121])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.80/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/1.48  
% 7.80/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.80/1.48  
% 7.80/1.48  ------  iProver source info
% 7.80/1.48  
% 7.80/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.80/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.80/1.48  git: non_committed_changes: false
% 7.80/1.48  git: last_make_outside_of_git: false
% 7.80/1.48  
% 7.80/1.48  ------ 
% 7.80/1.48  
% 7.80/1.48  ------ Input Options
% 7.80/1.48  
% 7.80/1.48  --out_options                           all
% 7.80/1.48  --tptp_safe_out                         true
% 7.80/1.48  --problem_path                          ""
% 7.80/1.48  --include_path                          ""
% 7.80/1.48  --clausifier                            res/vclausify_rel
% 7.80/1.48  --clausifier_options                    ""
% 7.80/1.48  --stdin                                 false
% 7.80/1.48  --stats_out                             all
% 7.80/1.48  
% 7.80/1.48  ------ General Options
% 7.80/1.48  
% 7.80/1.48  --fof                                   false
% 7.80/1.48  --time_out_real                         305.
% 7.80/1.48  --time_out_virtual                      -1.
% 7.80/1.48  --symbol_type_check                     false
% 7.80/1.48  --clausify_out                          false
% 7.80/1.48  --sig_cnt_out                           false
% 7.80/1.49  --trig_cnt_out                          false
% 7.80/1.49  --trig_cnt_out_tolerance                1.
% 7.80/1.49  --trig_cnt_out_sk_spl                   false
% 7.80/1.49  --abstr_cl_out                          false
% 7.80/1.49  
% 7.80/1.49  ------ Global Options
% 7.80/1.49  
% 7.80/1.49  --schedule                              default
% 7.80/1.49  --add_important_lit                     false
% 7.80/1.49  --prop_solver_per_cl                    1000
% 7.80/1.49  --min_unsat_core                        false
% 7.80/1.49  --soft_assumptions                      false
% 7.80/1.49  --soft_lemma_size                       3
% 7.80/1.49  --prop_impl_unit_size                   0
% 7.80/1.49  --prop_impl_unit                        []
% 7.80/1.49  --share_sel_clauses                     true
% 7.80/1.49  --reset_solvers                         false
% 7.80/1.49  --bc_imp_inh                            [conj_cone]
% 7.80/1.49  --conj_cone_tolerance                   3.
% 7.80/1.49  --extra_neg_conj                        none
% 7.80/1.49  --large_theory_mode                     true
% 7.80/1.49  --prolific_symb_bound                   200
% 7.80/1.49  --lt_threshold                          2000
% 7.80/1.49  --clause_weak_htbl                      true
% 7.80/1.49  --gc_record_bc_elim                     false
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing Options
% 7.80/1.49  
% 7.80/1.49  --preprocessing_flag                    true
% 7.80/1.49  --time_out_prep_mult                    0.1
% 7.80/1.49  --splitting_mode                        input
% 7.80/1.49  --splitting_grd                         true
% 7.80/1.49  --splitting_cvd                         false
% 7.80/1.49  --splitting_cvd_svl                     false
% 7.80/1.49  --splitting_nvd                         32
% 7.80/1.49  --sub_typing                            true
% 7.80/1.49  --prep_gs_sim                           true
% 7.80/1.49  --prep_unflatten                        true
% 7.80/1.49  --prep_res_sim                          true
% 7.80/1.49  --prep_upred                            true
% 7.80/1.49  --prep_sem_filter                       exhaustive
% 7.80/1.49  --prep_sem_filter_out                   false
% 7.80/1.49  --pred_elim                             true
% 7.80/1.49  --res_sim_input                         true
% 7.80/1.49  --eq_ax_congr_red                       true
% 7.80/1.49  --pure_diseq_elim                       true
% 7.80/1.49  --brand_transform                       false
% 7.80/1.49  --non_eq_to_eq                          false
% 7.80/1.49  --prep_def_merge                        true
% 7.80/1.49  --prep_def_merge_prop_impl              false
% 7.80/1.49  --prep_def_merge_mbd                    true
% 7.80/1.49  --prep_def_merge_tr_red                 false
% 7.80/1.49  --prep_def_merge_tr_cl                  false
% 7.80/1.49  --smt_preprocessing                     true
% 7.80/1.49  --smt_ac_axioms                         fast
% 7.80/1.49  --preprocessed_out                      false
% 7.80/1.49  --preprocessed_stats                    false
% 7.80/1.49  
% 7.80/1.49  ------ Abstraction refinement Options
% 7.80/1.49  
% 7.80/1.49  --abstr_ref                             []
% 7.80/1.49  --abstr_ref_prep                        false
% 7.80/1.49  --abstr_ref_until_sat                   false
% 7.80/1.49  --abstr_ref_sig_restrict                funpre
% 7.80/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.49  --abstr_ref_under                       []
% 7.80/1.49  
% 7.80/1.49  ------ SAT Options
% 7.80/1.49  
% 7.80/1.49  --sat_mode                              false
% 7.80/1.49  --sat_fm_restart_options                ""
% 7.80/1.49  --sat_gr_def                            false
% 7.80/1.49  --sat_epr_types                         true
% 7.80/1.49  --sat_non_cyclic_types                  false
% 7.80/1.49  --sat_finite_models                     false
% 7.80/1.49  --sat_fm_lemmas                         false
% 7.80/1.49  --sat_fm_prep                           false
% 7.80/1.49  --sat_fm_uc_incr                        true
% 7.80/1.49  --sat_out_model                         small
% 7.80/1.49  --sat_out_clauses                       false
% 7.80/1.49  
% 7.80/1.49  ------ QBF Options
% 7.80/1.49  
% 7.80/1.49  --qbf_mode                              false
% 7.80/1.49  --qbf_elim_univ                         false
% 7.80/1.49  --qbf_dom_inst                          none
% 7.80/1.49  --qbf_dom_pre_inst                      false
% 7.80/1.49  --qbf_sk_in                             false
% 7.80/1.49  --qbf_pred_elim                         true
% 7.80/1.49  --qbf_split                             512
% 7.80/1.49  
% 7.80/1.49  ------ BMC1 Options
% 7.80/1.49  
% 7.80/1.49  --bmc1_incremental                      false
% 7.80/1.49  --bmc1_axioms                           reachable_all
% 7.80/1.49  --bmc1_min_bound                        0
% 7.80/1.49  --bmc1_max_bound                        -1
% 7.80/1.49  --bmc1_max_bound_default                -1
% 7.80/1.49  --bmc1_symbol_reachability              true
% 7.80/1.49  --bmc1_property_lemmas                  false
% 7.80/1.49  --bmc1_k_induction                      false
% 7.80/1.49  --bmc1_non_equiv_states                 false
% 7.80/1.49  --bmc1_deadlock                         false
% 7.80/1.49  --bmc1_ucm                              false
% 7.80/1.49  --bmc1_add_unsat_core                   none
% 7.80/1.49  --bmc1_unsat_core_children              false
% 7.80/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.49  --bmc1_out_stat                         full
% 7.80/1.49  --bmc1_ground_init                      false
% 7.80/1.49  --bmc1_pre_inst_next_state              false
% 7.80/1.49  --bmc1_pre_inst_state                   false
% 7.80/1.49  --bmc1_pre_inst_reach_state             false
% 7.80/1.49  --bmc1_out_unsat_core                   false
% 7.80/1.49  --bmc1_aig_witness_out                  false
% 7.80/1.49  --bmc1_verbose                          false
% 7.80/1.49  --bmc1_dump_clauses_tptp                false
% 7.80/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.49  --bmc1_dump_file                        -
% 7.80/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.49  --bmc1_ucm_extend_mode                  1
% 7.80/1.49  --bmc1_ucm_init_mode                    2
% 7.80/1.49  --bmc1_ucm_cone_mode                    none
% 7.80/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.49  --bmc1_ucm_relax_model                  4
% 7.80/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.49  --bmc1_ucm_layered_model                none
% 7.80/1.49  --bmc1_ucm_max_lemma_size               10
% 7.80/1.49  
% 7.80/1.49  ------ AIG Options
% 7.80/1.49  
% 7.80/1.49  --aig_mode                              false
% 7.80/1.49  
% 7.80/1.49  ------ Instantiation Options
% 7.80/1.49  
% 7.80/1.49  --instantiation_flag                    true
% 7.80/1.49  --inst_sos_flag                         true
% 7.80/1.49  --inst_sos_phase                        true
% 7.80/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.49  --inst_lit_sel_side                     num_symb
% 7.80/1.49  --inst_solver_per_active                1400
% 7.80/1.49  --inst_solver_calls_frac                1.
% 7.80/1.49  --inst_passive_queue_type               priority_queues
% 7.80/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.49  --inst_passive_queues_freq              [25;2]
% 7.80/1.49  --inst_dismatching                      true
% 7.80/1.49  --inst_eager_unprocessed_to_passive     true
% 7.80/1.49  --inst_prop_sim_given                   true
% 7.80/1.49  --inst_prop_sim_new                     false
% 7.80/1.49  --inst_subs_new                         false
% 7.80/1.49  --inst_eq_res_simp                      false
% 7.80/1.49  --inst_subs_given                       false
% 7.80/1.49  --inst_orphan_elimination               true
% 7.80/1.49  --inst_learning_loop_flag               true
% 7.80/1.49  --inst_learning_start                   3000
% 7.80/1.49  --inst_learning_factor                  2
% 7.80/1.49  --inst_start_prop_sim_after_learn       3
% 7.80/1.49  --inst_sel_renew                        solver
% 7.80/1.49  --inst_lit_activity_flag                true
% 7.80/1.49  --inst_restr_to_given                   false
% 7.80/1.49  --inst_activity_threshold               500
% 7.80/1.49  --inst_out_proof                        true
% 7.80/1.49  
% 7.80/1.49  ------ Resolution Options
% 7.80/1.49  
% 7.80/1.49  --resolution_flag                       true
% 7.80/1.49  --res_lit_sel                           adaptive
% 7.80/1.49  --res_lit_sel_side                      none
% 7.80/1.49  --res_ordering                          kbo
% 7.80/1.49  --res_to_prop_solver                    active
% 7.80/1.49  --res_prop_simpl_new                    false
% 7.80/1.49  --res_prop_simpl_given                  true
% 7.80/1.49  --res_passive_queue_type                priority_queues
% 7.80/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.49  --res_passive_queues_freq               [15;5]
% 7.80/1.49  --res_forward_subs                      full
% 7.80/1.49  --res_backward_subs                     full
% 7.80/1.49  --res_forward_subs_resolution           true
% 7.80/1.49  --res_backward_subs_resolution          true
% 7.80/1.49  --res_orphan_elimination                true
% 7.80/1.49  --res_time_limit                        2.
% 7.80/1.49  --res_out_proof                         true
% 7.80/1.49  
% 7.80/1.49  ------ Superposition Options
% 7.80/1.49  
% 7.80/1.49  --superposition_flag                    true
% 7.80/1.49  --sup_passive_queue_type                priority_queues
% 7.80/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.49  --demod_completeness_check              fast
% 7.80/1.49  --demod_use_ground                      true
% 7.80/1.49  --sup_to_prop_solver                    passive
% 7.80/1.49  --sup_prop_simpl_new                    true
% 7.80/1.49  --sup_prop_simpl_given                  true
% 7.80/1.49  --sup_fun_splitting                     true
% 7.80/1.49  --sup_smt_interval                      50000
% 7.80/1.49  
% 7.80/1.49  ------ Superposition Simplification Setup
% 7.80/1.49  
% 7.80/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.80/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.80/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.80/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.80/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.80/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.80/1.49  --sup_immed_triv                        [TrivRules]
% 7.80/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.49  --sup_immed_bw_main                     []
% 7.80/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.80/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.49  --sup_input_bw                          []
% 7.80/1.49  
% 7.80/1.49  ------ Combination Options
% 7.80/1.49  
% 7.80/1.49  --comb_res_mult                         3
% 7.80/1.49  --comb_sup_mult                         2
% 7.80/1.49  --comb_inst_mult                        10
% 7.80/1.49  
% 7.80/1.49  ------ Debug Options
% 7.80/1.49  
% 7.80/1.49  --dbg_backtrace                         false
% 7.80/1.49  --dbg_dump_prop_clauses                 false
% 7.80/1.49  --dbg_dump_prop_clauses_file            -
% 7.80/1.49  --dbg_out_stat                          false
% 7.80/1.49  ------ Parsing...
% 7.80/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  ------ Proving...
% 7.80/1.49  ------ Problem Properties 
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  clauses                                 12
% 7.80/1.49  conjectures                             1
% 7.80/1.49  EPR                                     1
% 7.80/1.49  Horn                                    12
% 7.80/1.49  unary                                   7
% 7.80/1.49  binary                                  4
% 7.80/1.49  lits                                    18
% 7.80/1.49  lits eq                                 10
% 7.80/1.49  fd_pure                                 0
% 7.80/1.49  fd_pseudo                               0
% 7.80/1.49  fd_cond                                 0
% 7.80/1.49  fd_pseudo_cond                          0
% 7.80/1.49  AC symbols                              0
% 7.80/1.49  
% 7.80/1.49  ------ Schedule dynamic 5 is on 
% 7.80/1.49  
% 7.80/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ 
% 7.80/1.49  Current options:
% 7.80/1.49  ------ 
% 7.80/1.49  
% 7.80/1.49  ------ Input Options
% 7.80/1.49  
% 7.80/1.49  --out_options                           all
% 7.80/1.49  --tptp_safe_out                         true
% 7.80/1.49  --problem_path                          ""
% 7.80/1.49  --include_path                          ""
% 7.80/1.49  --clausifier                            res/vclausify_rel
% 7.80/1.49  --clausifier_options                    ""
% 7.80/1.49  --stdin                                 false
% 7.80/1.49  --stats_out                             all
% 7.80/1.49  
% 7.80/1.49  ------ General Options
% 7.80/1.49  
% 7.80/1.49  --fof                                   false
% 7.80/1.49  --time_out_real                         305.
% 7.80/1.49  --time_out_virtual                      -1.
% 7.80/1.49  --symbol_type_check                     false
% 7.80/1.49  --clausify_out                          false
% 7.80/1.49  --sig_cnt_out                           false
% 7.80/1.49  --trig_cnt_out                          false
% 7.80/1.49  --trig_cnt_out_tolerance                1.
% 7.80/1.49  --trig_cnt_out_sk_spl                   false
% 7.80/1.49  --abstr_cl_out                          false
% 7.80/1.49  
% 7.80/1.49  ------ Global Options
% 7.80/1.49  
% 7.80/1.49  --schedule                              default
% 7.80/1.49  --add_important_lit                     false
% 7.80/1.49  --prop_solver_per_cl                    1000
% 7.80/1.49  --min_unsat_core                        false
% 7.80/1.49  --soft_assumptions                      false
% 7.80/1.49  --soft_lemma_size                       3
% 7.80/1.49  --prop_impl_unit_size                   0
% 7.80/1.49  --prop_impl_unit                        []
% 7.80/1.49  --share_sel_clauses                     true
% 7.80/1.49  --reset_solvers                         false
% 7.80/1.49  --bc_imp_inh                            [conj_cone]
% 7.80/1.49  --conj_cone_tolerance                   3.
% 7.80/1.49  --extra_neg_conj                        none
% 7.80/1.49  --large_theory_mode                     true
% 7.80/1.49  --prolific_symb_bound                   200
% 7.80/1.49  --lt_threshold                          2000
% 7.80/1.49  --clause_weak_htbl                      true
% 7.80/1.49  --gc_record_bc_elim                     false
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing Options
% 7.80/1.49  
% 7.80/1.49  --preprocessing_flag                    true
% 7.80/1.49  --time_out_prep_mult                    0.1
% 7.80/1.49  --splitting_mode                        input
% 7.80/1.49  --splitting_grd                         true
% 7.80/1.49  --splitting_cvd                         false
% 7.80/1.49  --splitting_cvd_svl                     false
% 7.80/1.49  --splitting_nvd                         32
% 7.80/1.49  --sub_typing                            true
% 7.80/1.49  --prep_gs_sim                           true
% 7.80/1.49  --prep_unflatten                        true
% 7.80/1.49  --prep_res_sim                          true
% 7.80/1.49  --prep_upred                            true
% 7.80/1.49  --prep_sem_filter                       exhaustive
% 7.80/1.49  --prep_sem_filter_out                   false
% 7.80/1.49  --pred_elim                             true
% 7.80/1.49  --res_sim_input                         true
% 7.80/1.49  --eq_ax_congr_red                       true
% 7.80/1.49  --pure_diseq_elim                       true
% 7.80/1.49  --brand_transform                       false
% 7.80/1.49  --non_eq_to_eq                          false
% 7.80/1.49  --prep_def_merge                        true
% 7.80/1.49  --prep_def_merge_prop_impl              false
% 7.80/1.49  --prep_def_merge_mbd                    true
% 7.80/1.49  --prep_def_merge_tr_red                 false
% 7.80/1.49  --prep_def_merge_tr_cl                  false
% 7.80/1.49  --smt_preprocessing                     true
% 7.80/1.49  --smt_ac_axioms                         fast
% 7.80/1.49  --preprocessed_out                      false
% 7.80/1.49  --preprocessed_stats                    false
% 7.80/1.49  
% 7.80/1.49  ------ Abstraction refinement Options
% 7.80/1.49  
% 7.80/1.49  --abstr_ref                             []
% 7.80/1.49  --abstr_ref_prep                        false
% 7.80/1.49  --abstr_ref_until_sat                   false
% 7.80/1.49  --abstr_ref_sig_restrict                funpre
% 7.80/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.80/1.49  --abstr_ref_under                       []
% 7.80/1.49  
% 7.80/1.49  ------ SAT Options
% 7.80/1.49  
% 7.80/1.49  --sat_mode                              false
% 7.80/1.49  --sat_fm_restart_options                ""
% 7.80/1.49  --sat_gr_def                            false
% 7.80/1.49  --sat_epr_types                         true
% 7.80/1.49  --sat_non_cyclic_types                  false
% 7.80/1.49  --sat_finite_models                     false
% 7.80/1.49  --sat_fm_lemmas                         false
% 7.80/1.49  --sat_fm_prep                           false
% 7.80/1.49  --sat_fm_uc_incr                        true
% 7.80/1.49  --sat_out_model                         small
% 7.80/1.49  --sat_out_clauses                       false
% 7.80/1.49  
% 7.80/1.49  ------ QBF Options
% 7.80/1.49  
% 7.80/1.49  --qbf_mode                              false
% 7.80/1.49  --qbf_elim_univ                         false
% 7.80/1.49  --qbf_dom_inst                          none
% 7.80/1.49  --qbf_dom_pre_inst                      false
% 7.80/1.49  --qbf_sk_in                             false
% 7.80/1.49  --qbf_pred_elim                         true
% 7.80/1.49  --qbf_split                             512
% 7.80/1.49  
% 7.80/1.49  ------ BMC1 Options
% 7.80/1.49  
% 7.80/1.49  --bmc1_incremental                      false
% 7.80/1.49  --bmc1_axioms                           reachable_all
% 7.80/1.49  --bmc1_min_bound                        0
% 7.80/1.49  --bmc1_max_bound                        -1
% 7.80/1.49  --bmc1_max_bound_default                -1
% 7.80/1.49  --bmc1_symbol_reachability              true
% 7.80/1.49  --bmc1_property_lemmas                  false
% 7.80/1.49  --bmc1_k_induction                      false
% 7.80/1.49  --bmc1_non_equiv_states                 false
% 7.80/1.49  --bmc1_deadlock                         false
% 7.80/1.49  --bmc1_ucm                              false
% 7.80/1.49  --bmc1_add_unsat_core                   none
% 7.80/1.49  --bmc1_unsat_core_children              false
% 7.80/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.80/1.49  --bmc1_out_stat                         full
% 7.80/1.49  --bmc1_ground_init                      false
% 7.80/1.49  --bmc1_pre_inst_next_state              false
% 7.80/1.49  --bmc1_pre_inst_state                   false
% 7.80/1.49  --bmc1_pre_inst_reach_state             false
% 7.80/1.49  --bmc1_out_unsat_core                   false
% 7.80/1.49  --bmc1_aig_witness_out                  false
% 7.80/1.49  --bmc1_verbose                          false
% 7.80/1.49  --bmc1_dump_clauses_tptp                false
% 7.80/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.80/1.49  --bmc1_dump_file                        -
% 7.80/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.80/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.80/1.49  --bmc1_ucm_extend_mode                  1
% 7.80/1.49  --bmc1_ucm_init_mode                    2
% 7.80/1.49  --bmc1_ucm_cone_mode                    none
% 7.80/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.80/1.49  --bmc1_ucm_relax_model                  4
% 7.80/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.80/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.80/1.49  --bmc1_ucm_layered_model                none
% 7.80/1.49  --bmc1_ucm_max_lemma_size               10
% 7.80/1.49  
% 7.80/1.49  ------ AIG Options
% 7.80/1.49  
% 7.80/1.49  --aig_mode                              false
% 7.80/1.49  
% 7.80/1.49  ------ Instantiation Options
% 7.80/1.49  
% 7.80/1.49  --instantiation_flag                    true
% 7.80/1.49  --inst_sos_flag                         true
% 7.80/1.49  --inst_sos_phase                        true
% 7.80/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.80/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.80/1.49  --inst_lit_sel_side                     none
% 7.80/1.49  --inst_solver_per_active                1400
% 7.80/1.49  --inst_solver_calls_frac                1.
% 7.80/1.49  --inst_passive_queue_type               priority_queues
% 7.80/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.80/1.49  --inst_passive_queues_freq              [25;2]
% 7.80/1.49  --inst_dismatching                      true
% 7.80/1.49  --inst_eager_unprocessed_to_passive     true
% 7.80/1.49  --inst_prop_sim_given                   true
% 7.80/1.49  --inst_prop_sim_new                     false
% 7.80/1.49  --inst_subs_new                         false
% 7.80/1.49  --inst_eq_res_simp                      false
% 7.80/1.49  --inst_subs_given                       false
% 7.80/1.49  --inst_orphan_elimination               true
% 7.80/1.49  --inst_learning_loop_flag               true
% 7.80/1.49  --inst_learning_start                   3000
% 7.80/1.49  --inst_learning_factor                  2
% 7.80/1.49  --inst_start_prop_sim_after_learn       3
% 7.80/1.49  --inst_sel_renew                        solver
% 7.80/1.49  --inst_lit_activity_flag                true
% 7.80/1.49  --inst_restr_to_given                   false
% 7.80/1.49  --inst_activity_threshold               500
% 7.80/1.49  --inst_out_proof                        true
% 7.80/1.49  
% 7.80/1.49  ------ Resolution Options
% 7.80/1.49  
% 7.80/1.49  --resolution_flag                       false
% 7.80/1.49  --res_lit_sel                           adaptive
% 7.80/1.49  --res_lit_sel_side                      none
% 7.80/1.49  --res_ordering                          kbo
% 7.80/1.49  --res_to_prop_solver                    active
% 7.80/1.49  --res_prop_simpl_new                    false
% 7.80/1.49  --res_prop_simpl_given                  true
% 7.80/1.49  --res_passive_queue_type                priority_queues
% 7.80/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.80/1.49  --res_passive_queues_freq               [15;5]
% 7.80/1.49  --res_forward_subs                      full
% 7.80/1.49  --res_backward_subs                     full
% 7.80/1.49  --res_forward_subs_resolution           true
% 7.80/1.49  --res_backward_subs_resolution          true
% 7.80/1.49  --res_orphan_elimination                true
% 7.80/1.49  --res_time_limit                        2.
% 7.80/1.49  --res_out_proof                         true
% 7.80/1.49  
% 7.80/1.49  ------ Superposition Options
% 7.80/1.49  
% 7.80/1.49  --superposition_flag                    true
% 7.80/1.49  --sup_passive_queue_type                priority_queues
% 7.80/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.80/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.80/1.49  --demod_completeness_check              fast
% 7.80/1.49  --demod_use_ground                      true
% 7.80/1.49  --sup_to_prop_solver                    passive
% 7.80/1.49  --sup_prop_simpl_new                    true
% 7.80/1.49  --sup_prop_simpl_given                  true
% 7.80/1.49  --sup_fun_splitting                     true
% 7.80/1.49  --sup_smt_interval                      50000
% 7.80/1.49  
% 7.80/1.49  ------ Superposition Simplification Setup
% 7.80/1.49  
% 7.80/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.80/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.80/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.80/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.80/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.80/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.80/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.80/1.49  --sup_immed_triv                        [TrivRules]
% 7.80/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.49  --sup_immed_bw_main                     []
% 7.80/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.80/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.80/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.80/1.49  --sup_input_bw                          []
% 7.80/1.49  
% 7.80/1.49  ------ Combination Options
% 7.80/1.49  
% 7.80/1.49  --comb_res_mult                         3
% 7.80/1.49  --comb_sup_mult                         2
% 7.80/1.49  --comb_inst_mult                        10
% 7.80/1.49  
% 7.80/1.49  ------ Debug Options
% 7.80/1.49  
% 7.80/1.49  --dbg_backtrace                         false
% 7.80/1.49  --dbg_dump_prop_clauses                 false
% 7.80/1.49  --dbg_dump_prop_clauses_file            -
% 7.80/1.49  --dbg_out_stat                          false
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  % SZS status Theorem for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  fof(f4,axiom,(
% 7.80/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f27,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f4])).
% 7.80/1.49  
% 7.80/1.49  fof(f7,axiom,(
% 7.80/1.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f30,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.80/1.49    inference(cnf_transformation,[],[f7])).
% 7.80/1.49  
% 7.80/1.49  fof(f3,axiom,(
% 7.80/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f26,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.80/1.49    inference(cnf_transformation,[],[f3])).
% 7.80/1.49  
% 7.80/1.49  fof(f39,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f30,f26])).
% 7.80/1.49  
% 7.80/1.49  fof(f2,axiom,(
% 7.80/1.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f20,plain,(
% 7.80/1.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 7.80/1.49    inference(nnf_transformation,[],[f2])).
% 7.80/1.49  
% 7.80/1.49  fof(f24,plain,(
% 7.80/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f20])).
% 7.80/1.49  
% 7.80/1.49  fof(f38,plain,(
% 7.80/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f24,f26])).
% 7.80/1.49  
% 7.80/1.49  fof(f12,conjecture,(
% 7.80/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f13,negated_conjecture,(
% 7.80/1.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.80/1.49    inference(negated_conjecture,[],[f12])).
% 7.80/1.49  
% 7.80/1.49  fof(f19,plain,(
% 7.80/1.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.80/1.49    inference(ennf_transformation,[],[f13])).
% 7.80/1.49  
% 7.80/1.49  fof(f21,plain,(
% 7.80/1.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f22,plain,(
% 7.80/1.49    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 7.80/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21])).
% 7.80/1.49  
% 7.80/1.49  fof(f35,plain,(
% 7.80/1.49    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 7.80/1.49    inference(cnf_transformation,[],[f22])).
% 7.80/1.49  
% 7.80/1.49  fof(f42,plain,(
% 7.80/1.49    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 7.80/1.49    inference(definition_unfolding,[],[f35,f26])).
% 7.80/1.49  
% 7.80/1.49  fof(f5,axiom,(
% 7.80/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f16,plain,(
% 7.80/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.80/1.49    inference(ennf_transformation,[],[f5])).
% 7.80/1.49  
% 7.80/1.49  fof(f17,plain,(
% 7.80/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.80/1.49    inference(flattening,[],[f16])).
% 7.80/1.49  
% 7.80/1.49  fof(f28,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f17])).
% 7.80/1.49  
% 7.80/1.49  fof(f6,axiom,(
% 7.80/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f18,plain,(
% 7.80/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.80/1.49    inference(ennf_transformation,[],[f6])).
% 7.80/1.49  
% 7.80/1.49  fof(f29,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f18])).
% 7.80/1.49  
% 7.80/1.49  fof(f8,axiom,(
% 7.80/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f31,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f8])).
% 7.80/1.49  
% 7.80/1.49  fof(f40,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f31,f26,f26])).
% 7.80/1.49  
% 7.80/1.49  fof(f9,axiom,(
% 7.80/1.49    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f32,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.80/1.49    inference(cnf_transformation,[],[f9])).
% 7.80/1.49  
% 7.80/1.49  fof(f41,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f32,f26,f26,f26])).
% 7.80/1.49  
% 7.80/1.49  fof(f11,axiom,(
% 7.80/1.49    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f34,plain,(
% 7.80/1.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f11])).
% 7.80/1.49  
% 7.80/1.49  fof(f10,axiom,(
% 7.80/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f33,plain,(
% 7.80/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.80/1.49    inference(cnf_transformation,[],[f10])).
% 7.80/1.49  
% 7.80/1.49  fof(f1,axiom,(
% 7.80/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f14,plain,(
% 7.80/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 7.80/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 7.80/1.49  
% 7.80/1.49  fof(f15,plain,(
% 7.80/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 7.80/1.49    inference(ennf_transformation,[],[f14])).
% 7.80/1.49  
% 7.80/1.49  fof(f23,plain,(
% 7.80/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.80/1.49    inference(cnf_transformation,[],[f15])).
% 7.80/1.49  
% 7.80/1.49  fof(f36,plain,(
% 7.80/1.49    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 7.80/1.49    inference(cnf_transformation,[],[f22])).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3,plain,
% 7.80/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.80/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_6,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.80/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_2,plain,
% 7.80/1.49      ( r1_tarski(X0,X1)
% 7.80/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.80/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_385,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 7.80/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_717,plain,
% 7.80/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_6,c_385]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_12,negated_conjecture,
% 7.80/1.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 7.80/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_382,plain,
% 7.80/1.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4,plain,
% 7.80/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.80/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_384,plain,
% 7.80/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.80/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.80/1.49      | r1_tarski(X0,X2) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1120,plain,
% 7.80/1.49      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) != iProver_top
% 7.80/1.49      | r1_tarski(sK0,X0) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_382,c_384]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1319,plain,
% 7.80/1.49      ( r1_tarski(sK0,k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_717,c_1120]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5,plain,
% 7.80/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.80/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_383,plain,
% 7.80/1.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1377,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = sK0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1319,c_383]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_561,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_382,c_383]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_562,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)) = k3_xboole_0(sK0,X0) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_561,c_3]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_7,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.80/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_387,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_7,c_3]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1288,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(sK0,X0)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_562,c_387]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1302,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_1288,c_561]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_8,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
% 7.80/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_670,plain,
% 7.80/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X1))))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,X1)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_562,c_8]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1401,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1302,c_670]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1402,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_1401,c_561,c_562]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_10,plain,
% 7.80/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.80/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1403,plain,
% 7.80/1.49      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_1402,c_10]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1653,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1377,c_1403]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1654,plain,
% 7.80/1.49      ( k5_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = k2_xboole_0(k1_xboole_0,sK0) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_1653,c_1377]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_9,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.80/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1655,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,sK0) = sK0 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_1654,c_9,c_10]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_650,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1291,plain,
% 7.80/1.49      ( k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_561,c_387]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1298,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0)) = k3_xboole_0(X0,k5_xboole_0(sK0,sK0)) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_1291,c_561]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1299,plain,
% 7.80/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_1298,c_10]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1759,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = X0 ),
% 7.80/1.49      inference(light_normalisation,
% 7.80/1.49                [status(thm)],
% 7.80/1.49                [c_650,c_9,c_650,c_1299]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1909,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(X0,sK0)) = X0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1655,c_1759]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1910,plain,
% 7.80/1.49      ( k2_xboole_0(X0,k3_xboole_0(X0,sK0)) = X0 ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_1909,c_9,c_1299]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3267,plain,
% 7.80/1.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,sK0))) = k3_xboole_0(X0,X1) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3,c_1910]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_654,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))) = k2_xboole_0(k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)),k3_xboole_0(X0,X3)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_8,c_8]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4216,plain,
% 7.80/1.49      ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1302,c_654]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1783,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1759,c_1377]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4343,plain,
% 7.80/1.49      ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK0,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_4216,c_1403,c_1783]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1652,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k1_xboole_0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1299,c_1403]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1656,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_1652,c_9,c_10,c_1299]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_2050,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1656,c_1759]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_2051,plain,
% 7.80/1.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_2050,c_9,c_1299]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_2053,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_2051,c_6]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3285,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_2053,c_1759]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_737,plain,
% 7.80/1.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_717,c_383]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3318,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_3285,c_737]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4344,plain,
% 7.80/1.49      ( k2_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_4343,c_10,c_3318]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_20874,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k3_xboole_0(sK2,sK0)) = k3_xboole_0(sK0,sK2) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3267,c_4344]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_12887,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) = k2_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1302,c_4344]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_12916,plain,
% 7.80/1.49      ( k2_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_12887,c_1302]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_13957,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k3_xboole_0(sK0,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) = k1_xboole_0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_12916,c_6]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_669,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_562,c_3]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_823,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3,c_669]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_827,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_823,c_562]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_648,plain,
% 7.80/1.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_561,c_8]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4296,plain,
% 7.80/1.49      ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,X1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),sK0) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_654,c_648]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4305,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),sK0) = k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,X1)),sK0) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_4296,c_561]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1762,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) = X0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_6,c_1759]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_6297,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_4305,c_1762]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_9258,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)))),sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_562,c_6297]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_9337,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1)))),sK0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_9258,c_562]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1287,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3,c_387]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1303,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_1287,c_3]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1290,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,X3)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3,c_387]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1304,plain,
% 7.80/1.49      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_1303,c_1290]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_652,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X3)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3,c_8]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_656,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X3)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_652,c_387]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_7821,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_656,c_8]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_7893,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_7821,c_1304]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_9338,plain,
% 7.80/1.49      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(X0,X1))))),sK0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_9337,c_1304,c_3318,c_7893]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_9339,plain,
% 7.80/1.49      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),sK0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_9338,c_562]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_9577,plain,
% 7.80/1.49      ( k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))),k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))))),sK0)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_9339,c_9339]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3287,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_2053,c_8]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3319,plain,
% 7.80/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_3318,c_3287]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1768,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0),X1))) = sK0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_562,c_1759]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_2363,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)),X1))) = sK0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_562,c_1768]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3987,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),X0))) = sK0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_561,c_2363]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4007,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k2_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),X0)) = sK0 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_3987,c_10,c_3318]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1764,plain,
% 7.80/1.49      ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK0),k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),X1))) = sK0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_648,c_1759]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3723,plain,
% 7.80/1.49      ( k2_xboole_0(k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0),k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK0,sK0),X0))) = sK0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_561,c_1764]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_777,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK0))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_561,c_648]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_781,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0) = k5_xboole_0(sK0,k3_xboole_0(sK0,k1_xboole_0)) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_777,c_10]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1500,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0) = k5_xboole_0(sK0,k1_xboole_0) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_1299,c_781]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1501,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)),sK0) = sK0 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_1500,c_9]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3729,plain,
% 7.80/1.49      ( k2_xboole_0(sK0,k3_xboole_0(sK0,k2_xboole_0(k5_xboole_0(sK0,sK0),X0))) = sK0 ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_3723,c_1501]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3730,plain,
% 7.80/1.49      ( k2_xboole_0(sK0,k3_xboole_0(sK0,X0)) = sK0 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_3729,c_10,c_3318]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4457,plain,
% 7.80/1.49      ( k2_xboole_0(sK0,sK0) = sK0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_4007,c_3730]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_9640,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k3_xboole_0(X0,sK0)) = k3_xboole_0(sK0,X0) ),
% 7.80/1.49      inference(demodulation,
% 7.80/1.49                [status(thm)],
% 7.80/1.49                [c_9577,c_9,c_10,c_827,c_1299,c_3319,c_4457]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_10670,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_9640,c_387]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_10751,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) = k1_xboole_0 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_10670,c_10]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_649,plain,
% 7.80/1.49      ( k2_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)),k3_xboole_0(k3_xboole_0(X0,X1),X3)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_3,c_8]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_657,plain,
% 7.80/1.49      ( k2_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(k3_xboole_0(X0,X1),X3)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_649,c_3,c_387]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_11016,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK0,X0),X1)) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_10751,c_657]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_11082,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(X0,X1))) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_11016,c_827]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1651,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1302,c_1403]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1657,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)))) = k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_1651,c_1403]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1658,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ),
% 7.80/1.49      inference(light_normalisation,[status(thm)],[c_1657,c_1302]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1734,plain,
% 7.80/1.49      ( k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0))))) = k2_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_1302,c_1658]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1742,plain,
% 7.80/1.49      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ),
% 7.80/1.49      inference(light_normalisation,
% 7.80/1.49                [status(thm)],
% 7.80/1.49                [c_1734,c_1302,c_1403,c_1658]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_10695,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(X0,sK0)))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)))) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_9640,c_1742]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_10733,plain,
% 7.80/1.49      ( k5_xboole_0(sK0,k5_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_10695,c_9640]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_10734,plain,
% 7.80/1.49      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_10733,c_1403,c_3318]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_11083,plain,
% 7.80/1.49      ( k5_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1))))) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_11082,c_387,c_10734]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_13960,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,k3_xboole_0(sK2,X0)) = k1_xboole_0 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_13957,c_827,c_11083]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_20875,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_20874,c_13960]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1374,plain,
% 7.80/1.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_8,c_1319]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1629,plain,
% 7.80/1.49      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) = iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_6,c_1374]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1637,plain,
% 7.80/1.49      ( r1_tarski(sK0,sK1) = iProver_top ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_1629,c_9,c_1299]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_0,plain,
% 7.80/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.80/1.49      inference(cnf_transformation,[],[f23]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_11,negated_conjecture,
% 7.80/1.49      ( ~ r1_tarski(sK0,sK1) | ~ r1_xboole_0(sK0,sK2) ),
% 7.80/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_119,plain,
% 7.80/1.49      ( ~ r1_tarski(sK0,sK1)
% 7.80/1.49      | k3_xboole_0(X0,X1) != k1_xboole_0
% 7.80/1.49      | sK2 != X1
% 7.80/1.49      | sK0 != X0 ),
% 7.80/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_120,plain,
% 7.80/1.49      ( ~ r1_tarski(sK0,sK1) | k3_xboole_0(sK0,sK2) != k1_xboole_0 ),
% 7.80/1.49      inference(unflattening,[status(thm)],[c_119]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_121,plain,
% 7.80/1.49      ( k3_xboole_0(sK0,sK2) != k1_xboole_0
% 7.80/1.49      | r1_tarski(sK0,sK1) != iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_120]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(contradiction,plain,
% 7.80/1.49      ( $false ),
% 7.80/1.49      inference(minisat,[status(thm)],[c_20875,c_1637,c_121]) ).
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  ------                               Statistics
% 7.80/1.49  
% 7.80/1.49  ------ General
% 7.80/1.49  
% 7.80/1.49  abstr_ref_over_cycles:                  0
% 7.80/1.49  abstr_ref_under_cycles:                 0
% 7.80/1.49  gc_basic_clause_elim:                   0
% 7.80/1.49  forced_gc_time:                         0
% 7.80/1.49  parsing_time:                           0.013
% 7.80/1.49  unif_index_cands_time:                  0.
% 7.80/1.49  unif_index_add_time:                    0.
% 7.80/1.49  orderings_time:                         0.
% 7.80/1.49  out_proof_time:                         0.012
% 7.80/1.49  total_time:                             0.782
% 7.80/1.49  num_of_symbols:                         40
% 7.80/1.49  num_of_terms:                           34124
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing
% 7.80/1.49  
% 7.80/1.49  num_of_splits:                          0
% 7.80/1.49  num_of_split_atoms:                     0
% 7.80/1.49  num_of_reused_defs:                     0
% 7.80/1.49  num_eq_ax_congr_red:                    0
% 7.80/1.49  num_of_sem_filtered_clauses:            1
% 7.80/1.49  num_of_subtypes:                        0
% 7.80/1.49  monotx_restored_types:                  0
% 7.80/1.49  sat_num_of_epr_types:                   0
% 7.80/1.49  sat_num_of_non_cyclic_types:            0
% 7.80/1.49  sat_guarded_non_collapsed_types:        0
% 7.80/1.49  num_pure_diseq_elim:                    0
% 7.80/1.49  simp_replaced_by:                       0
% 7.80/1.49  res_preprocessed:                       62
% 7.80/1.49  prep_upred:                             0
% 7.80/1.49  prep_unflattend:                        2
% 7.80/1.49  smt_new_axioms:                         0
% 7.80/1.49  pred_elim_cands:                        1
% 7.80/1.49  pred_elim:                              1
% 7.80/1.49  pred_elim_cl:                           1
% 7.80/1.49  pred_elim_cycles:                       3
% 7.80/1.49  merged_defs:                            8
% 7.80/1.49  merged_defs_ncl:                        0
% 7.80/1.49  bin_hyper_res:                          8
% 7.80/1.49  prep_cycles:                            4
% 7.80/1.49  pred_elim_time:                         0.
% 7.80/1.49  splitting_time:                         0.
% 7.80/1.49  sem_filter_time:                        0.
% 7.80/1.49  monotx_time:                            0.
% 7.80/1.49  subtype_inf_time:                       0.
% 7.80/1.49  
% 7.80/1.49  ------ Problem properties
% 7.80/1.49  
% 7.80/1.49  clauses:                                12
% 7.80/1.49  conjectures:                            1
% 7.80/1.49  epr:                                    1
% 7.80/1.49  horn:                                   12
% 7.80/1.49  ground:                                 2
% 7.80/1.49  unary:                                  7
% 7.80/1.49  binary:                                 4
% 7.80/1.49  lits:                                   18
% 7.80/1.49  lits_eq:                                10
% 7.80/1.49  fd_pure:                                0
% 7.80/1.49  fd_pseudo:                              0
% 7.80/1.49  fd_cond:                                0
% 7.80/1.49  fd_pseudo_cond:                         0
% 7.80/1.49  ac_symbols:                             0
% 7.80/1.49  
% 7.80/1.49  ------ Propositional Solver
% 7.80/1.49  
% 7.80/1.49  prop_solver_calls:                      34
% 7.80/1.49  prop_fast_solver_calls:                 397
% 7.80/1.49  smt_solver_calls:                       0
% 7.80/1.49  smt_fast_solver_calls:                  0
% 7.80/1.49  prop_num_of_clauses:                    7090
% 7.80/1.49  prop_preprocess_simplified:             7867
% 7.80/1.49  prop_fo_subsumed:                       0
% 7.80/1.49  prop_solver_time:                       0.
% 7.80/1.49  smt_solver_time:                        0.
% 7.80/1.49  smt_fast_solver_time:                   0.
% 7.80/1.49  prop_fast_solver_time:                  0.
% 7.80/1.49  prop_unsat_core_time:                   0.
% 7.80/1.49  
% 7.80/1.49  ------ QBF
% 7.80/1.49  
% 7.80/1.49  qbf_q_res:                              0
% 7.80/1.49  qbf_num_tautologies:                    0
% 7.80/1.49  qbf_prep_cycles:                        0
% 7.80/1.49  
% 7.80/1.49  ------ BMC1
% 7.80/1.49  
% 7.80/1.49  bmc1_current_bound:                     -1
% 7.80/1.49  bmc1_last_solved_bound:                 -1
% 7.80/1.49  bmc1_unsat_core_size:                   -1
% 7.80/1.49  bmc1_unsat_core_parents_size:           -1
% 7.80/1.49  bmc1_merge_next_fun:                    0
% 7.80/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.80/1.49  
% 7.80/1.49  ------ Instantiation
% 7.80/1.49  
% 7.80/1.49  inst_num_of_clauses:                    1543
% 7.80/1.49  inst_num_in_passive:                    851
% 7.80/1.49  inst_num_in_active:                     565
% 7.80/1.49  inst_num_in_unprocessed:                128
% 7.80/1.49  inst_num_of_loops:                      720
% 7.80/1.49  inst_num_of_learning_restarts:          0
% 7.80/1.49  inst_num_moves_active_passive:          149
% 7.80/1.49  inst_lit_activity:                      0
% 7.80/1.49  inst_lit_activity_moves:                0
% 7.80/1.49  inst_num_tautologies:                   0
% 7.80/1.49  inst_num_prop_implied:                  0
% 7.80/1.49  inst_num_existing_simplified:           0
% 7.80/1.49  inst_num_eq_res_simplified:             0
% 7.80/1.49  inst_num_child_elim:                    0
% 7.80/1.49  inst_num_of_dismatching_blockings:      1212
% 7.80/1.49  inst_num_of_non_proper_insts:           1488
% 7.80/1.49  inst_num_of_duplicates:                 0
% 7.80/1.49  inst_inst_num_from_inst_to_res:         0
% 7.80/1.49  inst_dismatching_checking_time:         0.
% 7.80/1.49  
% 7.80/1.49  ------ Resolution
% 7.80/1.49  
% 7.80/1.49  res_num_of_clauses:                     0
% 7.80/1.49  res_num_in_passive:                     0
% 7.80/1.49  res_num_in_active:                      0
% 7.80/1.49  res_num_of_loops:                       66
% 7.80/1.49  res_forward_subset_subsumed:            197
% 7.80/1.49  res_backward_subset_subsumed:           4
% 7.80/1.49  res_forward_subsumed:                   0
% 7.80/1.49  res_backward_subsumed:                  0
% 7.80/1.49  res_forward_subsumption_resolution:     0
% 7.80/1.49  res_backward_subsumption_resolution:    0
% 7.80/1.49  res_clause_to_clause_subsumption:       6035
% 7.80/1.49  res_orphan_elimination:                 0
% 7.80/1.49  res_tautology_del:                      260
% 7.80/1.49  res_num_eq_res_simplified:              0
% 7.80/1.49  res_num_sel_changes:                    0
% 7.80/1.49  res_moves_from_active_to_pass:          0
% 7.80/1.49  
% 7.80/1.49  ------ Superposition
% 7.80/1.49  
% 7.80/1.49  sup_time_total:                         0.
% 7.80/1.49  sup_time_generating:                    0.
% 7.80/1.49  sup_time_sim_full:                      0.
% 7.80/1.49  sup_time_sim_immed:                     0.
% 7.80/1.49  
% 7.80/1.49  sup_num_of_clauses:                     1640
% 7.80/1.49  sup_num_in_active:                      107
% 7.80/1.49  sup_num_in_passive:                     1533
% 7.80/1.49  sup_num_of_loops:                       142
% 7.80/1.49  sup_fw_superposition:                   3058
% 7.80/1.49  sup_bw_superposition:                   1888
% 7.80/1.49  sup_immediate_simplified:               2956
% 7.80/1.49  sup_given_eliminated:                   7
% 7.80/1.49  comparisons_done:                       0
% 7.80/1.49  comparisons_avoided:                    0
% 7.80/1.49  
% 7.80/1.49  ------ Simplifications
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  sim_fw_subset_subsumed:                 7
% 7.80/1.49  sim_bw_subset_subsumed:                 0
% 7.80/1.49  sim_fw_subsumed:                        354
% 7.80/1.49  sim_bw_subsumed:                        69
% 7.80/1.49  sim_fw_subsumption_res:                 0
% 7.80/1.49  sim_bw_subsumption_res:                 0
% 7.80/1.49  sim_tautology_del:                      3
% 7.80/1.49  sim_eq_tautology_del:                   1052
% 7.80/1.49  sim_eq_res_simp:                        24
% 7.80/1.49  sim_fw_demodulated:                     2349
% 7.80/1.49  sim_bw_demodulated:                     128
% 7.80/1.49  sim_light_normalised:                   1326
% 7.80/1.49  sim_joinable_taut:                      0
% 7.80/1.49  sim_joinable_simp:                      0
% 7.80/1.49  sim_ac_normalised:                      0
% 7.80/1.49  sim_smt_subsumption:                    0
% 7.80/1.49  
%------------------------------------------------------------------------------
