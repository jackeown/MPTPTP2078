%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:42 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 540 expanded)
%              Number of clauses        :   77 ( 221 expanded)
%              Number of leaves         :   13 ( 136 expanded)
%              Depth                    :   21
%              Number of atoms          :  145 ( 765 expanded)
%              Number of equality atoms :  120 ( 614 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f28,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f29,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_11,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_122,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_674,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_122])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_676,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_674,c_4])).

cnf(c_1687,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_676])).

cnf(c_2039,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_1687])).

cnf(c_2377,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2039,c_4])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2379,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2377,c_2])).

cnf(c_671,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_682,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_671,c_6])).

cnf(c_5514,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(X0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2379,c_682])).

cnf(c_11435,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK2,sK1))) = k4_xboole_0(X0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_0,c_5514])).

cnf(c_1698,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_676,c_4])).

cnf(c_1703,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1698,c_2])).

cnf(c_4187,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_11,c_1703])).

cnf(c_4210,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4187,c_1703])).

cnf(c_11497,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(X0,k2_xboole_0(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_11435,c_4210])).

cnf(c_673,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_3605,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_122,c_673])).

cnf(c_3686,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3605,c_2])).

cnf(c_11545,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)),X0),k2_xboole_0(sK0,sK1))) = X0 ),
    inference(superposition,[status(thm)],[c_11497,c_3686])).

cnf(c_4183,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1703])).

cnf(c_12374,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4183,c_0])).

cnf(c_21954,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),k2_xboole_0(sK0,sK1))) = X0 ),
    inference(demodulation,[status(thm)],[c_11545,c_12374])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1691,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_676])).

cnf(c_3619,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(X0,k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK1,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_11,c_673])).

cnf(c_3654,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(X0,sK0)) = k2_xboole_0(sK1,k4_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_3619,c_673])).

cnf(c_4583,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK1,k4_xboole_0(X0,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3654,c_676])).

cnf(c_5085,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK2),k2_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1691,c_4583])).

cnf(c_5113,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X0,sK2),sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5085,c_2,c_6])).

cnf(c_12851,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(X0,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_5113])).

cnf(c_22595,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK0,sK1)) = k2_xboole_0(k2_xboole_0(X0,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12851,c_673])).

cnf(c_357,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_107,plain,
    ( r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_109,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_520,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_107,c_109])).

cnf(c_925,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_520,c_7])).

cnf(c_1097,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_357,c_925])).

cnf(c_22598,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK2),sK0) = k2_xboole_0(k2_xboole_0(X0,sK2),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_22595,c_1097])).

cnf(c_22599,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK2),sK0) = k2_xboole_0(X0,sK2) ),
    inference(demodulation,[status(thm)],[c_22598,c_2])).

cnf(c_26143,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),sK0) = k2_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_0,c_22599])).

cnf(c_26705,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_26143,c_0])).

cnf(c_29959,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK2),k2_xboole_0(sK0,sK1)),sK2) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_21954,c_26705])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_108,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_519,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_108,c_109])).

cnf(c_823,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_519,c_7])).

cnf(c_938,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_357,c_823])).

cnf(c_1319,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_938,c_6])).

cnf(c_2946,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1319])).

cnf(c_6643,plain,
    ( k4_xboole_0(sK2,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2946,c_2039])).

cnf(c_6949,plain,
    ( k2_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6643,c_4])).

cnf(c_6961,plain,
    ( k2_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_6949,c_2])).

cnf(c_30002,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK2),k2_xboole_0(sK0,sK1)),sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_29959,c_6961])).

cnf(c_6948,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_6643,c_6])).

cnf(c_1689,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_676])).

cnf(c_6964,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6948,c_1689])).

cnf(c_7669,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,X0),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK0,X0),sK2) ),
    inference(superposition,[status(thm)],[c_6964,c_4])).

cnf(c_7677,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,X0),sK2) = k2_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_7669,c_2])).

cnf(c_18162,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK0),sK2) = k2_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_7677])).

cnf(c_30003,plain,
    ( sK2 = sK0 ),
    inference(demodulation,[status(thm)],[c_30002,c_122,c_357,c_18162])).

cnf(c_45,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_175,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_46,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_162,plain,
    ( sK2 != X0
    | sK0 != X0
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_174,plain,
    ( sK2 != sK0
    | sK0 = sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_8,negated_conjecture,
    ( sK0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30003,c_175,c_174,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.67/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/1.50  
% 7.67/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.50  
% 7.67/1.50  ------  iProver source info
% 7.67/1.50  
% 7.67/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.50  git: non_committed_changes: false
% 7.67/1.50  git: last_make_outside_of_git: false
% 7.67/1.50  
% 7.67/1.50  ------ 
% 7.67/1.50  ------ Parsing...
% 7.67/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.50  
% 7.67/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.50  ------ Proving...
% 7.67/1.50  ------ Problem Properties 
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  clauses                                 12
% 7.67/1.50  conjectures                             4
% 7.67/1.50  EPR                                     3
% 7.67/1.50  Horn                                    12
% 7.67/1.50  unary                                   11
% 7.67/1.50  binary                                  1
% 7.67/1.50  lits                                    13
% 7.67/1.50  lits eq                                 10
% 7.67/1.50  fd_pure                                 0
% 7.67/1.50  fd_pseudo                               0
% 7.67/1.50  fd_cond                                 0
% 7.67/1.50  fd_pseudo_cond                          0
% 7.67/1.50  AC symbols                              0
% 7.67/1.50  
% 7.67/1.50  ------ Input Options Time Limit: Unbounded
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  ------ 
% 7.67/1.50  Current options:
% 7.67/1.50  ------ 
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  ------ Proving...
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  % SZS status Theorem for theBenchmark.p
% 7.67/1.50  
% 7.67/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.50  
% 7.67/1.50  fof(f1,axiom,(
% 7.67/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f18,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f1])).
% 7.67/1.50  
% 7.67/1.50  fof(f10,conjecture,(
% 7.67/1.50    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f11,negated_conjecture,(
% 7.67/1.50    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 7.67/1.50    inference(negated_conjecture,[],[f10])).
% 7.67/1.50  
% 7.67/1.50  fof(f14,plain,(
% 7.67/1.50    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 7.67/1.50    inference(ennf_transformation,[],[f11])).
% 7.67/1.50  
% 7.67/1.50  fof(f15,plain,(
% 7.67/1.50    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 7.67/1.50    inference(flattening,[],[f14])).
% 7.67/1.50  
% 7.67/1.50  fof(f16,plain,(
% 7.67/1.50    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 7.67/1.50    introduced(choice_axiom,[])).
% 7.67/1.50  
% 7.67/1.50  fof(f17,plain,(
% 7.67/1.50    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 7.67/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).
% 7.67/1.50  
% 7.67/1.50  fof(f27,plain,(
% 7.67/1.50    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 7.67/1.50    inference(cnf_transformation,[],[f17])).
% 7.67/1.50  
% 7.67/1.50  fof(f7,axiom,(
% 7.67/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f24,plain,(
% 7.67/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f7])).
% 7.67/1.50  
% 7.67/1.50  fof(f4,axiom,(
% 7.67/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f21,plain,(
% 7.67/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.67/1.50    inference(cnf_transformation,[],[f4])).
% 7.67/1.50  
% 7.67/1.50  fof(f8,axiom,(
% 7.67/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f25,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.67/1.50    inference(cnf_transformation,[],[f8])).
% 7.67/1.50  
% 7.67/1.50  fof(f32,plain,(
% 7.67/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.67/1.50    inference(definition_unfolding,[],[f21,f25])).
% 7.67/1.50  
% 7.67/1.50  fof(f6,axiom,(
% 7.67/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f23,plain,(
% 7.67/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.67/1.50    inference(cnf_transformation,[],[f6])).
% 7.67/1.50  
% 7.67/1.50  fof(f5,axiom,(
% 7.67/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f22,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.67/1.50    inference(cnf_transformation,[],[f5])).
% 7.67/1.50  
% 7.67/1.50  fof(f3,axiom,(
% 7.67/1.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f20,plain,(
% 7.67/1.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.67/1.50    inference(cnf_transformation,[],[f3])).
% 7.67/1.50  
% 7.67/1.50  fof(f9,axiom,(
% 7.67/1.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f26,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.67/1.50    inference(cnf_transformation,[],[f9])).
% 7.67/1.50  
% 7.67/1.50  fof(f33,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 7.67/1.50    inference(definition_unfolding,[],[f26,f25])).
% 7.67/1.50  
% 7.67/1.50  fof(f28,plain,(
% 7.67/1.50    r1_xboole_0(sK0,sK1)),
% 7.67/1.50    inference(cnf_transformation,[],[f17])).
% 7.67/1.50  
% 7.67/1.50  fof(f2,axiom,(
% 7.67/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.67/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.50  
% 7.67/1.50  fof(f12,plain,(
% 7.67/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.67/1.50    inference(unused_predicate_definition_removal,[],[f2])).
% 7.67/1.50  
% 7.67/1.50  fof(f13,plain,(
% 7.67/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 7.67/1.50    inference(ennf_transformation,[],[f12])).
% 7.67/1.50  
% 7.67/1.50  fof(f19,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.67/1.50    inference(cnf_transformation,[],[f13])).
% 7.67/1.50  
% 7.67/1.50  fof(f31,plain,(
% 7.67/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.67/1.50    inference(definition_unfolding,[],[f19,f25])).
% 7.67/1.50  
% 7.67/1.50  fof(f29,plain,(
% 7.67/1.50    r1_xboole_0(sK2,sK1)),
% 7.67/1.50    inference(cnf_transformation,[],[f17])).
% 7.67/1.50  
% 7.67/1.50  fof(f30,plain,(
% 7.67/1.50    sK0 != sK2),
% 7.67/1.50    inference(cnf_transformation,[],[f17])).
% 7.67/1.50  
% 7.67/1.50  cnf(c_0,plain,
% 7.67/1.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(cnf_transformation,[],[f18]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_11,negated_conjecture,
% 7.67/1.50      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
% 7.67/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_6,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.67/1.50      inference(cnf_transformation,[],[f24]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.67/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_5,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.67/1.50      inference(cnf_transformation,[],[f23]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_122,plain,
% 7.67/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_674,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_6,c_122]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(cnf_transformation,[],[f22]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_676,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_674,c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1687,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_676]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2039,plain,
% 7.67/1.50      ( k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_11,c_1687]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2377,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_2039,c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.67/1.50      inference(cnf_transformation,[],[f20]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2379,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(sK0,sK1) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_2377,c_2]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_671,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_682,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_671,c_6]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_5514,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(X0,k2_xboole_0(sK0,sK1)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_2379,c_682]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_11435,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK2,sK1))) = k4_xboole_0(X0,k2_xboole_0(sK0,sK1)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_5514]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1698,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_676,c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1703,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_1698,c_2]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4187,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(sK0,sK1),sK1) = k2_xboole_0(sK2,sK1) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_11,c_1703]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4210,plain,
% 7.67/1.50      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK0,sK1) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_4187,c_1703]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_11497,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(X0,k2_xboole_0(sK0,sK1)) ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_11435,c_4210]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_673,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3605,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_122,c_673]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3686,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X1)) = X0 ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_3605,c_2]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_11545,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)),X0),k2_xboole_0(sK0,sK1))) = X0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_11497,c_3686]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4183,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_1703]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_12374,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_4183,c_0]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_21954,plain,
% 7.67/1.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),X0),k2_xboole_0(sK0,sK1))) = X0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_11545,c_12374]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_7,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.67/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1691,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_7,c_676]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3619,plain,
% 7.67/1.50      ( k2_xboole_0(sK1,k4_xboole_0(X0,k2_xboole_0(sK0,sK1))) = k2_xboole_0(sK1,k4_xboole_0(X0,sK2)) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_11,c_673]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_3654,plain,
% 7.67/1.50      ( k2_xboole_0(sK1,k4_xboole_0(X0,sK0)) = k2_xboole_0(sK1,k4_xboole_0(X0,sK2)) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_3619,c_673]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_4583,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(X0,sK2),k2_xboole_0(sK1,k4_xboole_0(X0,sK0))) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_3654,c_676]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_5085,plain,
% 7.67/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),sK2),k2_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_1691,c_4583]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_5113,plain,
% 7.67/1.50      ( k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(X0,sK2),sK1)) = k1_xboole_0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_5085,c_2,c_6]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_12851,plain,
% 7.67/1.50      ( k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(X0,sK2))) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_5113]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_22595,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK0,sK1)) = k2_xboole_0(k2_xboole_0(X0,sK2),k1_xboole_0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_12851,c_673]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_357,plain,
% 7.67/1.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_10,negated_conjecture,
% 7.67/1.50      ( r1_xboole_0(sK0,sK1) ),
% 7.67/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_107,plain,
% 7.67/1.50      ( r1_xboole_0(sK0,sK1) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1,plain,
% 7.67/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.67/1.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.67/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_109,plain,
% 7.67/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.67/1.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_520,plain,
% 7.67/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_107,c_109]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_925,plain,
% 7.67/1.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) = sK0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_520,c_7]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1097,plain,
% 7.67/1.50      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_357,c_925]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_22598,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,sK2),sK0) = k2_xboole_0(k2_xboole_0(X0,sK2),k1_xboole_0) ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_22595,c_1097]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_22599,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,sK2),sK0) = k2_xboole_0(X0,sK2) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_22598,c_2]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_26143,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(sK2,X0),sK0) = k2_xboole_0(X0,sK2) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_22599]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_26705,plain,
% 7.67/1.50      ( k2_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,sK2) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_26143,c_0]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_29959,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK2),k2_xboole_0(sK0,sK1)),sK2) = k2_xboole_0(sK0,sK2) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_21954,c_26705]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_9,negated_conjecture,
% 7.67/1.50      ( r1_xboole_0(sK2,sK1) ),
% 7.67/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_108,plain,
% 7.67/1.50      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 7.67/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_519,plain,
% 7.67/1.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_108,c_109]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_823,plain,
% 7.67/1.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = sK2 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_519,c_7]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_938,plain,
% 7.67/1.50      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_357,c_823]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1319,plain,
% 7.67/1.50      ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_938,c_6]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_2946,plain,
% 7.67/1.50      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK1)) = k4_xboole_0(sK2,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_1319]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_6643,plain,
% 7.67/1.50      ( k4_xboole_0(sK2,sK0) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_2946,c_2039]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_6949,plain,
% 7.67/1.50      ( k2_xboole_0(sK0,sK2) = k2_xboole_0(sK0,k1_xboole_0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_6643,c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_6961,plain,
% 7.67/1.50      ( k2_xboole_0(sK0,sK2) = sK0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_6949,c_2]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_30002,plain,
% 7.67/1.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK2),k2_xboole_0(sK0,sK1)),sK2) = sK0 ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_29959,c_6961]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_6948,plain,
% 7.67/1.50      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_6643,c_6]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_1689,plain,
% 7.67/1.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_2,c_676]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_6964,plain,
% 7.67/1.50      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k1_xboole_0 ),
% 7.67/1.50      inference(light_normalisation,[status(thm)],[c_6948,c_1689]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_7669,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(sK0,X0),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK0,X0),sK2) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_6964,c_4]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_7677,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(sK0,X0),sK2) = k2_xboole_0(sK0,X0) ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_7669,c_2]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_18162,plain,
% 7.67/1.50      ( k2_xboole_0(k2_xboole_0(X0,sK0),sK2) = k2_xboole_0(sK0,X0) ),
% 7.67/1.50      inference(superposition,[status(thm)],[c_0,c_7677]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_30003,plain,
% 7.67/1.50      ( sK2 = sK0 ),
% 7.67/1.50      inference(demodulation,[status(thm)],[c_30002,c_122,c_357,c_18162]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_45,plain,( X0 = X0 ),theory(equality) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_175,plain,
% 7.67/1.50      ( sK0 = sK0 ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_45]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_46,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_162,plain,
% 7.67/1.50      ( sK2 != X0 | sK0 != X0 | sK0 = sK2 ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_46]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_174,plain,
% 7.67/1.50      ( sK2 != sK0 | sK0 = sK2 | sK0 != sK0 ),
% 7.67/1.50      inference(instantiation,[status(thm)],[c_162]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(c_8,negated_conjecture,
% 7.67/1.50      ( sK0 != sK2 ),
% 7.67/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.67/1.50  
% 7.67/1.50  cnf(contradiction,plain,
% 7.67/1.50      ( $false ),
% 7.67/1.50      inference(minisat,[status(thm)],[c_30003,c_175,c_174,c_8]) ).
% 7.67/1.50  
% 7.67/1.50  
% 7.67/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.50  
% 7.67/1.50  ------                               Statistics
% 7.67/1.50  
% 7.67/1.50  ------ Selected
% 7.67/1.50  
% 7.67/1.50  total_time:                             0.775
% 7.67/1.50  
%------------------------------------------------------------------------------
