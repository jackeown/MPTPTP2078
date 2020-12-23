%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:47 EST 2020

% Result     : Theorem 15.41s
% Output     : CNFRefutation 15.41s
% Verified   : 
% Statistics : Number of formulae       :  182 (7667 expanded)
%              Number of clauses        :  141 (3048 expanded)
%              Number of leaves         :   16 (1807 expanded)
%              Depth                    :   31
%              Number of atoms          :  233 (14026 expanded)
%              Number of equality atoms :  190 (9134 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,
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

fof(f22,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).

fof(f35,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f32,f32])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f32])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_141,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_9,c_0])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_474,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_141,c_6])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_588,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_595,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_588,c_6])).

cnf(c_7295,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK3),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK3),k4_xboole_0(sK2,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) ),
    inference(superposition,[status(thm)],[c_474,c_595])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_576,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_5946,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK3),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK1,sK0),sK3))) ),
    inference(superposition,[status(thm)],[c_474,c_576])).

cnf(c_7345,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK1,sK0),sK3)))) = k4_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_7295,c_474,c_5946])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_220,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_381,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_220])).

cnf(c_2134,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_141,c_381])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_223,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2160,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_2134,c_223])).

cnf(c_2305,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2160,c_6])).

cnf(c_383,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_141,c_220])).

cnf(c_1008,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_383,c_223])).

cnf(c_1287,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1008,c_6])).

cnf(c_2317,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2305,c_1287])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_221,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_464,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_141,c_221])).

cnf(c_762,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_220,c_464])).

cnf(c_1010,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_762,c_223])).

cnf(c_1680,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1010,c_9])).

cnf(c_229,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_2673,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_141,c_229])).

cnf(c_3129,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_2673,c_229])).

cnf(c_14683,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1680,c_3129])).

cnf(c_1683,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_1010,c_0])).

cnf(c_14686,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_14683,c_141,c_1683,c_2160])).

cnf(c_24504,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_7345,c_2317,c_7345,c_14686])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_475,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_476,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_475,c_5])).

cnf(c_3115,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_476,c_2673])).

cnf(c_3400,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK1,sK0)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_3115,c_6])).

cnf(c_1102,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_476,c_0])).

cnf(c_3409,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_3115,c_1102])).

cnf(c_3435,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_3400,c_1287,c_3409])).

cnf(c_661,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_141,c_9])).

cnf(c_758,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_661,c_9])).

cnf(c_2949,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1683,c_758])).

cnf(c_2950,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_2949,c_141])).

cnf(c_228,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_3202,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2950,c_228])).

cnf(c_230,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_3855,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,X0),X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_2673,c_230])).

cnf(c_14682,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1680,c_3855])).

cnf(c_14687,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_14682,c_141,c_2160])).

cnf(c_14961,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2)),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_14687,c_9])).

cnf(c_14970,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2)),X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_14687,c_230])).

cnf(c_14760,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_14686,c_9])).

cnf(c_15634,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) ),
    inference(superposition,[status(thm)],[c_1683,c_14760])).

cnf(c_15709,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_15634,c_14686])).

cnf(c_755,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_661,c_0])).

cnf(c_904,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_755,c_9])).

cnf(c_20453,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_904,c_230])).

cnf(c_1800,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_228,c_755])).

cnf(c_3134,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_2673,c_228])).

cnf(c_10001,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3134,c_230])).

cnf(c_3893,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_230,c_2673])).

cnf(c_4813,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_230,c_3893])).

cnf(c_10025,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_10001,c_4813])).

cnf(c_20647,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(X0,X1),sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_20453,c_1800,c_10025])).

cnf(c_20464,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X0)))) = k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_904,c_1680])).

cnf(c_15665,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_14760,c_230])).

cnf(c_20632,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X0)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(light_normalisation,[status(thm)],[c_20464,c_15665])).

cnf(c_14670,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,X1))) = k2_xboole_0(X0,k2_xboole_0(sK3,X1)) ),
    inference(superposition,[status(thm)],[c_1680,c_228])).

cnf(c_20633,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK3,X0),sK0))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(demodulation,[status(thm)],[c_20632,c_1800,c_14670])).

cnf(c_20657,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(X0,sK3)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(demodulation,[status(thm)],[c_20647,c_20633])).

cnf(c_2146,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_381,c_464])).

cnf(c_2300,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2146,c_223])).

cnf(c_2503,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2300,c_9])).

cnf(c_3856,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_2300,c_230])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_102,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_103,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_584,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_103,c_8])).

cnf(c_597,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_584,c_5])).

cnf(c_581,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_12790,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_597,c_581])).

cnf(c_590,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_103,c_8])).

cnf(c_591,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_590,c_103])).

cnf(c_592,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_591,c_5])).

cnf(c_12864,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_12790,c_592])).

cnf(c_12865,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_12864,c_5])).

cnf(c_15984,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_2503,c_3856,c_12865])).

cnf(c_15995,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_0,c_15984])).

cnf(c_20663,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(light_normalisation,[status(thm)],[c_20657,c_15995])).

cnf(c_20664,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(demodulation,[status(thm)],[c_20663,c_14670])).

cnf(c_22790,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) = k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_14961,c_14970,c_15709,c_20664])).

cnf(c_22798,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK3,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_3202,c_22790])).

cnf(c_22909,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK3,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_22798,c_2160])).

cnf(c_3194,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_2950,c_9])).

cnf(c_11470,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_0,c_3194])).

cnf(c_16041,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_15984,c_228])).

cnf(c_22910,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_22909,c_11470,c_16041])).

cnf(c_22911,plain,
    ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_22910,c_1683])).

cnf(c_24505,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_24504,c_3435,c_22911])).

cnf(c_24506,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK3)))) = k4_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_24505,c_22911])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_222,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_462,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_221])).

cnf(c_4875,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_141,c_462])).

cnf(c_5438,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_222,c_4875])).

cnf(c_6494,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_5438,c_223])).

cnf(c_51840,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_6494,c_6494,c_22911])).

cnf(c_51880,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_51840,c_0])).

cnf(c_52121,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_24506,c_51880])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_97,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_98,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_97])).

cnf(c_577,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_98])).

cnf(c_850,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_577,c_8])).

cnf(c_851,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_850,c_5])).

cnf(c_906,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_755,c_6])).

cnf(c_25301,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK3)),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_906,c_906,c_22911])).

cnf(c_3903,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_230,c_6])).

cnf(c_25302,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_25301,c_3903])).

cnf(c_25319,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1683,c_25302])).

cnf(c_25373,plain,
    ( k4_xboole_0(sK2,sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_25319,c_851,c_1683])).

cnf(c_4859,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_383,c_462])).

cnf(c_4905,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4859,c_597])).

cnf(c_35738,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4905,c_223])).

cnf(c_52203,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_52121,c_851,c_25373,c_35738])).

cnf(c_144,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_232,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_233,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_143,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_151,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_11,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52203,c_233,c_151,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.41/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.41/2.50  
% 15.41/2.50  ------  iProver source info
% 15.41/2.50  
% 15.41/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.41/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.41/2.50  git: non_committed_changes: false
% 15.41/2.50  git: last_make_outside_of_git: false
% 15.41/2.50  
% 15.41/2.50  ------ 
% 15.41/2.50  
% 15.41/2.50  ------ Input Options
% 15.41/2.50  
% 15.41/2.50  --out_options                           all
% 15.41/2.50  --tptp_safe_out                         true
% 15.41/2.50  --problem_path                          ""
% 15.41/2.50  --include_path                          ""
% 15.41/2.50  --clausifier                            res/vclausify_rel
% 15.41/2.50  --clausifier_options                    ""
% 15.41/2.50  --stdin                                 false
% 15.41/2.50  --stats_out                             all
% 15.41/2.50  
% 15.41/2.50  ------ General Options
% 15.41/2.50  
% 15.41/2.50  --fof                                   false
% 15.41/2.50  --time_out_real                         305.
% 15.41/2.50  --time_out_virtual                      -1.
% 15.41/2.50  --symbol_type_check                     false
% 15.41/2.50  --clausify_out                          false
% 15.41/2.50  --sig_cnt_out                           false
% 15.41/2.50  --trig_cnt_out                          false
% 15.41/2.50  --trig_cnt_out_tolerance                1.
% 15.41/2.50  --trig_cnt_out_sk_spl                   false
% 15.41/2.50  --abstr_cl_out                          false
% 15.41/2.50  
% 15.41/2.50  ------ Global Options
% 15.41/2.50  
% 15.41/2.50  --schedule                              default
% 15.41/2.50  --add_important_lit                     false
% 15.41/2.50  --prop_solver_per_cl                    1000
% 15.41/2.50  --min_unsat_core                        false
% 15.41/2.50  --soft_assumptions                      false
% 15.41/2.50  --soft_lemma_size                       3
% 15.41/2.50  --prop_impl_unit_size                   0
% 15.41/2.50  --prop_impl_unit                        []
% 15.41/2.50  --share_sel_clauses                     true
% 15.41/2.50  --reset_solvers                         false
% 15.41/2.50  --bc_imp_inh                            [conj_cone]
% 15.41/2.50  --conj_cone_tolerance                   3.
% 15.41/2.50  --extra_neg_conj                        none
% 15.41/2.50  --large_theory_mode                     true
% 15.41/2.50  --prolific_symb_bound                   200
% 15.41/2.50  --lt_threshold                          2000
% 15.41/2.50  --clause_weak_htbl                      true
% 15.41/2.50  --gc_record_bc_elim                     false
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing Options
% 15.41/2.50  
% 15.41/2.50  --preprocessing_flag                    true
% 15.41/2.50  --time_out_prep_mult                    0.1
% 15.41/2.50  --splitting_mode                        input
% 15.41/2.50  --splitting_grd                         true
% 15.41/2.50  --splitting_cvd                         false
% 15.41/2.50  --splitting_cvd_svl                     false
% 15.41/2.50  --splitting_nvd                         32
% 15.41/2.50  --sub_typing                            true
% 15.41/2.50  --prep_gs_sim                           true
% 15.41/2.50  --prep_unflatten                        true
% 15.41/2.50  --prep_res_sim                          true
% 15.41/2.50  --prep_upred                            true
% 15.41/2.50  --prep_sem_filter                       exhaustive
% 15.41/2.50  --prep_sem_filter_out                   false
% 15.41/2.50  --pred_elim                             true
% 15.41/2.50  --res_sim_input                         true
% 15.41/2.50  --eq_ax_congr_red                       true
% 15.41/2.50  --pure_diseq_elim                       true
% 15.41/2.50  --brand_transform                       false
% 15.41/2.50  --non_eq_to_eq                          false
% 15.41/2.50  --prep_def_merge                        true
% 15.41/2.50  --prep_def_merge_prop_impl              false
% 15.41/2.50  --prep_def_merge_mbd                    true
% 15.41/2.50  --prep_def_merge_tr_red                 false
% 15.41/2.50  --prep_def_merge_tr_cl                  false
% 15.41/2.50  --smt_preprocessing                     true
% 15.41/2.50  --smt_ac_axioms                         fast
% 15.41/2.50  --preprocessed_out                      false
% 15.41/2.50  --preprocessed_stats                    false
% 15.41/2.50  
% 15.41/2.50  ------ Abstraction refinement Options
% 15.41/2.50  
% 15.41/2.50  --abstr_ref                             []
% 15.41/2.50  --abstr_ref_prep                        false
% 15.41/2.50  --abstr_ref_until_sat                   false
% 15.41/2.50  --abstr_ref_sig_restrict                funpre
% 15.41/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.41/2.50  --abstr_ref_under                       []
% 15.41/2.50  
% 15.41/2.50  ------ SAT Options
% 15.41/2.50  
% 15.41/2.50  --sat_mode                              false
% 15.41/2.50  --sat_fm_restart_options                ""
% 15.41/2.50  --sat_gr_def                            false
% 15.41/2.50  --sat_epr_types                         true
% 15.41/2.50  --sat_non_cyclic_types                  false
% 15.41/2.50  --sat_finite_models                     false
% 15.41/2.50  --sat_fm_lemmas                         false
% 15.41/2.50  --sat_fm_prep                           false
% 15.41/2.50  --sat_fm_uc_incr                        true
% 15.41/2.50  --sat_out_model                         small
% 15.41/2.50  --sat_out_clauses                       false
% 15.41/2.50  
% 15.41/2.50  ------ QBF Options
% 15.41/2.50  
% 15.41/2.50  --qbf_mode                              false
% 15.41/2.50  --qbf_elim_univ                         false
% 15.41/2.50  --qbf_dom_inst                          none
% 15.41/2.50  --qbf_dom_pre_inst                      false
% 15.41/2.50  --qbf_sk_in                             false
% 15.41/2.50  --qbf_pred_elim                         true
% 15.41/2.50  --qbf_split                             512
% 15.41/2.50  
% 15.41/2.50  ------ BMC1 Options
% 15.41/2.50  
% 15.41/2.50  --bmc1_incremental                      false
% 15.41/2.50  --bmc1_axioms                           reachable_all
% 15.41/2.50  --bmc1_min_bound                        0
% 15.41/2.50  --bmc1_max_bound                        -1
% 15.41/2.50  --bmc1_max_bound_default                -1
% 15.41/2.50  --bmc1_symbol_reachability              true
% 15.41/2.50  --bmc1_property_lemmas                  false
% 15.41/2.50  --bmc1_k_induction                      false
% 15.41/2.50  --bmc1_non_equiv_states                 false
% 15.41/2.50  --bmc1_deadlock                         false
% 15.41/2.50  --bmc1_ucm                              false
% 15.41/2.50  --bmc1_add_unsat_core                   none
% 15.41/2.50  --bmc1_unsat_core_children              false
% 15.41/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.41/2.50  --bmc1_out_stat                         full
% 15.41/2.50  --bmc1_ground_init                      false
% 15.41/2.50  --bmc1_pre_inst_next_state              false
% 15.41/2.50  --bmc1_pre_inst_state                   false
% 15.41/2.50  --bmc1_pre_inst_reach_state             false
% 15.41/2.50  --bmc1_out_unsat_core                   false
% 15.41/2.50  --bmc1_aig_witness_out                  false
% 15.41/2.50  --bmc1_verbose                          false
% 15.41/2.50  --bmc1_dump_clauses_tptp                false
% 15.41/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.41/2.50  --bmc1_dump_file                        -
% 15.41/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.41/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.41/2.50  --bmc1_ucm_extend_mode                  1
% 15.41/2.50  --bmc1_ucm_init_mode                    2
% 15.41/2.50  --bmc1_ucm_cone_mode                    none
% 15.41/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.41/2.50  --bmc1_ucm_relax_model                  4
% 15.41/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.41/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.41/2.50  --bmc1_ucm_layered_model                none
% 15.41/2.50  --bmc1_ucm_max_lemma_size               10
% 15.41/2.50  
% 15.41/2.50  ------ AIG Options
% 15.41/2.50  
% 15.41/2.50  --aig_mode                              false
% 15.41/2.50  
% 15.41/2.50  ------ Instantiation Options
% 15.41/2.50  
% 15.41/2.50  --instantiation_flag                    true
% 15.41/2.50  --inst_sos_flag                         true
% 15.41/2.50  --inst_sos_phase                        true
% 15.41/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.41/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.41/2.50  --inst_lit_sel_side                     num_symb
% 15.41/2.50  --inst_solver_per_active                1400
% 15.41/2.50  --inst_solver_calls_frac                1.
% 15.41/2.50  --inst_passive_queue_type               priority_queues
% 15.41/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.41/2.50  --inst_passive_queues_freq              [25;2]
% 15.41/2.50  --inst_dismatching                      true
% 15.41/2.50  --inst_eager_unprocessed_to_passive     true
% 15.41/2.50  --inst_prop_sim_given                   true
% 15.41/2.50  --inst_prop_sim_new                     false
% 15.41/2.50  --inst_subs_new                         false
% 15.41/2.50  --inst_eq_res_simp                      false
% 15.41/2.50  --inst_subs_given                       false
% 15.41/2.50  --inst_orphan_elimination               true
% 15.41/2.50  --inst_learning_loop_flag               true
% 15.41/2.50  --inst_learning_start                   3000
% 15.41/2.50  --inst_learning_factor                  2
% 15.41/2.50  --inst_start_prop_sim_after_learn       3
% 15.41/2.50  --inst_sel_renew                        solver
% 15.41/2.50  --inst_lit_activity_flag                true
% 15.41/2.50  --inst_restr_to_given                   false
% 15.41/2.50  --inst_activity_threshold               500
% 15.41/2.50  --inst_out_proof                        true
% 15.41/2.50  
% 15.41/2.50  ------ Resolution Options
% 15.41/2.50  
% 15.41/2.50  --resolution_flag                       true
% 15.41/2.50  --res_lit_sel                           adaptive
% 15.41/2.50  --res_lit_sel_side                      none
% 15.41/2.50  --res_ordering                          kbo
% 15.41/2.50  --res_to_prop_solver                    active
% 15.41/2.50  --res_prop_simpl_new                    false
% 15.41/2.50  --res_prop_simpl_given                  true
% 15.41/2.50  --res_passive_queue_type                priority_queues
% 15.41/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.41/2.50  --res_passive_queues_freq               [15;5]
% 15.41/2.50  --res_forward_subs                      full
% 15.41/2.50  --res_backward_subs                     full
% 15.41/2.50  --res_forward_subs_resolution           true
% 15.41/2.50  --res_backward_subs_resolution          true
% 15.41/2.50  --res_orphan_elimination                true
% 15.41/2.50  --res_time_limit                        2.
% 15.41/2.50  --res_out_proof                         true
% 15.41/2.50  
% 15.41/2.50  ------ Superposition Options
% 15.41/2.50  
% 15.41/2.50  --superposition_flag                    true
% 15.41/2.50  --sup_passive_queue_type                priority_queues
% 15.41/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.41/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.41/2.50  --demod_completeness_check              fast
% 15.41/2.50  --demod_use_ground                      true
% 15.41/2.50  --sup_to_prop_solver                    passive
% 15.41/2.50  --sup_prop_simpl_new                    true
% 15.41/2.50  --sup_prop_simpl_given                  true
% 15.41/2.50  --sup_fun_splitting                     true
% 15.41/2.50  --sup_smt_interval                      50000
% 15.41/2.50  
% 15.41/2.50  ------ Superposition Simplification Setup
% 15.41/2.50  
% 15.41/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.41/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.41/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.41/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.41/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.41/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.41/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.41/2.50  --sup_immed_triv                        [TrivRules]
% 15.41/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.50  --sup_immed_bw_main                     []
% 15.41/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.41/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.41/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.50  --sup_input_bw                          []
% 15.41/2.50  
% 15.41/2.50  ------ Combination Options
% 15.41/2.50  
% 15.41/2.50  --comb_res_mult                         3
% 15.41/2.50  --comb_sup_mult                         2
% 15.41/2.50  --comb_inst_mult                        10
% 15.41/2.50  
% 15.41/2.50  ------ Debug Options
% 15.41/2.50  
% 15.41/2.50  --dbg_backtrace                         false
% 15.41/2.50  --dbg_dump_prop_clauses                 false
% 15.41/2.50  --dbg_dump_prop_clauses_file            -
% 15.41/2.50  --dbg_out_stat                          false
% 15.41/2.50  ------ Parsing...
% 15.41/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.41/2.50  ------ Proving...
% 15.41/2.50  ------ Problem Properties 
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  clauses                                 14
% 15.41/2.50  conjectures                             2
% 15.41/2.50  EPR                                     1
% 15.41/2.50  Horn                                    14
% 15.41/2.50  unary                                   12
% 15.41/2.50  binary                                  2
% 15.41/2.50  lits                                    16
% 15.41/2.50  lits eq                                 11
% 15.41/2.50  fd_pure                                 0
% 15.41/2.50  fd_pseudo                               0
% 15.41/2.50  fd_cond                                 0
% 15.41/2.50  fd_pseudo_cond                          0
% 15.41/2.50  AC symbols                              1
% 15.41/2.50  
% 15.41/2.50  ------ Schedule dynamic 5 is on 
% 15.41/2.50  
% 15.41/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  ------ 
% 15.41/2.50  Current options:
% 15.41/2.50  ------ 
% 15.41/2.50  
% 15.41/2.50  ------ Input Options
% 15.41/2.50  
% 15.41/2.50  --out_options                           all
% 15.41/2.50  --tptp_safe_out                         true
% 15.41/2.50  --problem_path                          ""
% 15.41/2.50  --include_path                          ""
% 15.41/2.50  --clausifier                            res/vclausify_rel
% 15.41/2.50  --clausifier_options                    ""
% 15.41/2.50  --stdin                                 false
% 15.41/2.50  --stats_out                             all
% 15.41/2.50  
% 15.41/2.50  ------ General Options
% 15.41/2.50  
% 15.41/2.50  --fof                                   false
% 15.41/2.50  --time_out_real                         305.
% 15.41/2.50  --time_out_virtual                      -1.
% 15.41/2.50  --symbol_type_check                     false
% 15.41/2.50  --clausify_out                          false
% 15.41/2.50  --sig_cnt_out                           false
% 15.41/2.50  --trig_cnt_out                          false
% 15.41/2.50  --trig_cnt_out_tolerance                1.
% 15.41/2.50  --trig_cnt_out_sk_spl                   false
% 15.41/2.50  --abstr_cl_out                          false
% 15.41/2.50  
% 15.41/2.50  ------ Global Options
% 15.41/2.50  
% 15.41/2.50  --schedule                              default
% 15.41/2.50  --add_important_lit                     false
% 15.41/2.50  --prop_solver_per_cl                    1000
% 15.41/2.50  --min_unsat_core                        false
% 15.41/2.50  --soft_assumptions                      false
% 15.41/2.50  --soft_lemma_size                       3
% 15.41/2.50  --prop_impl_unit_size                   0
% 15.41/2.50  --prop_impl_unit                        []
% 15.41/2.50  --share_sel_clauses                     true
% 15.41/2.50  --reset_solvers                         false
% 15.41/2.50  --bc_imp_inh                            [conj_cone]
% 15.41/2.50  --conj_cone_tolerance                   3.
% 15.41/2.50  --extra_neg_conj                        none
% 15.41/2.50  --large_theory_mode                     true
% 15.41/2.50  --prolific_symb_bound                   200
% 15.41/2.50  --lt_threshold                          2000
% 15.41/2.50  --clause_weak_htbl                      true
% 15.41/2.50  --gc_record_bc_elim                     false
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing Options
% 15.41/2.50  
% 15.41/2.50  --preprocessing_flag                    true
% 15.41/2.50  --time_out_prep_mult                    0.1
% 15.41/2.50  --splitting_mode                        input
% 15.41/2.50  --splitting_grd                         true
% 15.41/2.50  --splitting_cvd                         false
% 15.41/2.50  --splitting_cvd_svl                     false
% 15.41/2.50  --splitting_nvd                         32
% 15.41/2.50  --sub_typing                            true
% 15.41/2.50  --prep_gs_sim                           true
% 15.41/2.50  --prep_unflatten                        true
% 15.41/2.50  --prep_res_sim                          true
% 15.41/2.50  --prep_upred                            true
% 15.41/2.50  --prep_sem_filter                       exhaustive
% 15.41/2.50  --prep_sem_filter_out                   false
% 15.41/2.50  --pred_elim                             true
% 15.41/2.50  --res_sim_input                         true
% 15.41/2.50  --eq_ax_congr_red                       true
% 15.41/2.50  --pure_diseq_elim                       true
% 15.41/2.50  --brand_transform                       false
% 15.41/2.50  --non_eq_to_eq                          false
% 15.41/2.50  --prep_def_merge                        true
% 15.41/2.50  --prep_def_merge_prop_impl              false
% 15.41/2.50  --prep_def_merge_mbd                    true
% 15.41/2.50  --prep_def_merge_tr_red                 false
% 15.41/2.50  --prep_def_merge_tr_cl                  false
% 15.41/2.50  --smt_preprocessing                     true
% 15.41/2.50  --smt_ac_axioms                         fast
% 15.41/2.50  --preprocessed_out                      false
% 15.41/2.50  --preprocessed_stats                    false
% 15.41/2.50  
% 15.41/2.50  ------ Abstraction refinement Options
% 15.41/2.50  
% 15.41/2.50  --abstr_ref                             []
% 15.41/2.50  --abstr_ref_prep                        false
% 15.41/2.50  --abstr_ref_until_sat                   false
% 15.41/2.50  --abstr_ref_sig_restrict                funpre
% 15.41/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.41/2.50  --abstr_ref_under                       []
% 15.41/2.50  
% 15.41/2.50  ------ SAT Options
% 15.41/2.50  
% 15.41/2.50  --sat_mode                              false
% 15.41/2.50  --sat_fm_restart_options                ""
% 15.41/2.50  --sat_gr_def                            false
% 15.41/2.50  --sat_epr_types                         true
% 15.41/2.50  --sat_non_cyclic_types                  false
% 15.41/2.50  --sat_finite_models                     false
% 15.41/2.50  --sat_fm_lemmas                         false
% 15.41/2.50  --sat_fm_prep                           false
% 15.41/2.50  --sat_fm_uc_incr                        true
% 15.41/2.50  --sat_out_model                         small
% 15.41/2.50  --sat_out_clauses                       false
% 15.41/2.50  
% 15.41/2.50  ------ QBF Options
% 15.41/2.50  
% 15.41/2.50  --qbf_mode                              false
% 15.41/2.50  --qbf_elim_univ                         false
% 15.41/2.50  --qbf_dom_inst                          none
% 15.41/2.50  --qbf_dom_pre_inst                      false
% 15.41/2.50  --qbf_sk_in                             false
% 15.41/2.50  --qbf_pred_elim                         true
% 15.41/2.50  --qbf_split                             512
% 15.41/2.50  
% 15.41/2.50  ------ BMC1 Options
% 15.41/2.50  
% 15.41/2.50  --bmc1_incremental                      false
% 15.41/2.50  --bmc1_axioms                           reachable_all
% 15.41/2.50  --bmc1_min_bound                        0
% 15.41/2.50  --bmc1_max_bound                        -1
% 15.41/2.50  --bmc1_max_bound_default                -1
% 15.41/2.50  --bmc1_symbol_reachability              true
% 15.41/2.50  --bmc1_property_lemmas                  false
% 15.41/2.50  --bmc1_k_induction                      false
% 15.41/2.50  --bmc1_non_equiv_states                 false
% 15.41/2.50  --bmc1_deadlock                         false
% 15.41/2.50  --bmc1_ucm                              false
% 15.41/2.50  --bmc1_add_unsat_core                   none
% 15.41/2.50  --bmc1_unsat_core_children              false
% 15.41/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.41/2.50  --bmc1_out_stat                         full
% 15.41/2.50  --bmc1_ground_init                      false
% 15.41/2.50  --bmc1_pre_inst_next_state              false
% 15.41/2.50  --bmc1_pre_inst_state                   false
% 15.41/2.50  --bmc1_pre_inst_reach_state             false
% 15.41/2.50  --bmc1_out_unsat_core                   false
% 15.41/2.50  --bmc1_aig_witness_out                  false
% 15.41/2.50  --bmc1_verbose                          false
% 15.41/2.50  --bmc1_dump_clauses_tptp                false
% 15.41/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.41/2.50  --bmc1_dump_file                        -
% 15.41/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.41/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.41/2.50  --bmc1_ucm_extend_mode                  1
% 15.41/2.50  --bmc1_ucm_init_mode                    2
% 15.41/2.50  --bmc1_ucm_cone_mode                    none
% 15.41/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.41/2.50  --bmc1_ucm_relax_model                  4
% 15.41/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.41/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.41/2.50  --bmc1_ucm_layered_model                none
% 15.41/2.50  --bmc1_ucm_max_lemma_size               10
% 15.41/2.50  
% 15.41/2.50  ------ AIG Options
% 15.41/2.50  
% 15.41/2.50  --aig_mode                              false
% 15.41/2.50  
% 15.41/2.50  ------ Instantiation Options
% 15.41/2.50  
% 15.41/2.50  --instantiation_flag                    true
% 15.41/2.50  --inst_sos_flag                         true
% 15.41/2.50  --inst_sos_phase                        true
% 15.41/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.41/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.41/2.50  --inst_lit_sel_side                     none
% 15.41/2.50  --inst_solver_per_active                1400
% 15.41/2.50  --inst_solver_calls_frac                1.
% 15.41/2.50  --inst_passive_queue_type               priority_queues
% 15.41/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.41/2.50  --inst_passive_queues_freq              [25;2]
% 15.41/2.50  --inst_dismatching                      true
% 15.41/2.50  --inst_eager_unprocessed_to_passive     true
% 15.41/2.50  --inst_prop_sim_given                   true
% 15.41/2.50  --inst_prop_sim_new                     false
% 15.41/2.50  --inst_subs_new                         false
% 15.41/2.50  --inst_eq_res_simp                      false
% 15.41/2.50  --inst_subs_given                       false
% 15.41/2.50  --inst_orphan_elimination               true
% 15.41/2.50  --inst_learning_loop_flag               true
% 15.41/2.50  --inst_learning_start                   3000
% 15.41/2.50  --inst_learning_factor                  2
% 15.41/2.50  --inst_start_prop_sim_after_learn       3
% 15.41/2.50  --inst_sel_renew                        solver
% 15.41/2.50  --inst_lit_activity_flag                true
% 15.41/2.50  --inst_restr_to_given                   false
% 15.41/2.50  --inst_activity_threshold               500
% 15.41/2.50  --inst_out_proof                        true
% 15.41/2.50  
% 15.41/2.50  ------ Resolution Options
% 15.41/2.50  
% 15.41/2.50  --resolution_flag                       false
% 15.41/2.50  --res_lit_sel                           adaptive
% 15.41/2.50  --res_lit_sel_side                      none
% 15.41/2.50  --res_ordering                          kbo
% 15.41/2.50  --res_to_prop_solver                    active
% 15.41/2.50  --res_prop_simpl_new                    false
% 15.41/2.50  --res_prop_simpl_given                  true
% 15.41/2.50  --res_passive_queue_type                priority_queues
% 15.41/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.41/2.50  --res_passive_queues_freq               [15;5]
% 15.41/2.50  --res_forward_subs                      full
% 15.41/2.50  --res_backward_subs                     full
% 15.41/2.50  --res_forward_subs_resolution           true
% 15.41/2.50  --res_backward_subs_resolution          true
% 15.41/2.50  --res_orphan_elimination                true
% 15.41/2.50  --res_time_limit                        2.
% 15.41/2.50  --res_out_proof                         true
% 15.41/2.50  
% 15.41/2.50  ------ Superposition Options
% 15.41/2.50  
% 15.41/2.50  --superposition_flag                    true
% 15.41/2.50  --sup_passive_queue_type                priority_queues
% 15.41/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.41/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.41/2.50  --demod_completeness_check              fast
% 15.41/2.50  --demod_use_ground                      true
% 15.41/2.50  --sup_to_prop_solver                    passive
% 15.41/2.50  --sup_prop_simpl_new                    true
% 15.41/2.50  --sup_prop_simpl_given                  true
% 15.41/2.50  --sup_fun_splitting                     true
% 15.41/2.50  --sup_smt_interval                      50000
% 15.41/2.50  
% 15.41/2.50  ------ Superposition Simplification Setup
% 15.41/2.50  
% 15.41/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.41/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.41/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.41/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.41/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.41/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.41/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.41/2.50  --sup_immed_triv                        [TrivRules]
% 15.41/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.50  --sup_immed_bw_main                     []
% 15.41/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.41/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.41/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.41/2.50  --sup_input_bw                          []
% 15.41/2.50  
% 15.41/2.50  ------ Combination Options
% 15.41/2.50  
% 15.41/2.50  --comb_res_mult                         3
% 15.41/2.50  --comb_sup_mult                         2
% 15.41/2.50  --comb_inst_mult                        10
% 15.41/2.50  
% 15.41/2.50  ------ Debug Options
% 15.41/2.50  
% 15.41/2.50  --dbg_backtrace                         false
% 15.41/2.50  --dbg_dump_prop_clauses                 false
% 15.41/2.50  --dbg_dump_prop_clauses_file            -
% 15.41/2.50  --dbg_out_stat                          false
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  ------ Proving...
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  % SZS status Theorem for theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  fof(f13,conjecture,(
% 15.41/2.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f14,negated_conjecture,(
% 15.41/2.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 15.41/2.50    inference(negated_conjecture,[],[f13])).
% 15.41/2.50  
% 15.41/2.50  fof(f19,plain,(
% 15.41/2.50    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 15.41/2.50    inference(ennf_transformation,[],[f14])).
% 15.41/2.50  
% 15.41/2.50  fof(f20,plain,(
% 15.41/2.50    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 15.41/2.50    inference(flattening,[],[f19])).
% 15.41/2.50  
% 15.41/2.50  fof(f21,plain,(
% 15.41/2.50    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 15.41/2.50    introduced(choice_axiom,[])).
% 15.41/2.50  
% 15.41/2.50  fof(f22,plain,(
% 15.41/2.50    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 15.41/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 15.41/2.50  
% 15.41/2.50  fof(f35,plain,(
% 15.41/2.50    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 15.41/2.50    inference(cnf_transformation,[],[f22])).
% 15.41/2.50  
% 15.41/2.50  fof(f11,axiom,(
% 15.41/2.50    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f33,plain,(
% 15.41/2.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f11])).
% 15.41/2.50  
% 15.41/2.50  fof(f1,axiom,(
% 15.41/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f23,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f1])).
% 15.41/2.50  
% 15.41/2.50  fof(f7,axiom,(
% 15.41/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f29,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f7])).
% 15.41/2.50  
% 15.41/2.50  fof(f9,axiom,(
% 15.41/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f31,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f9])).
% 15.41/2.50  
% 15.41/2.50  fof(f10,axiom,(
% 15.41/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f32,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f10])).
% 15.41/2.50  
% 15.41/2.50  fof(f41,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.41/2.50    inference(definition_unfolding,[],[f31,f32])).
% 15.41/2.50  
% 15.41/2.50  fof(f2,axiom,(
% 15.41/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f24,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f2])).
% 15.41/2.50  
% 15.41/2.50  fof(f39,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.41/2.50    inference(definition_unfolding,[],[f24,f32,f32])).
% 15.41/2.50  
% 15.41/2.50  fof(f12,axiom,(
% 15.41/2.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f34,plain,(
% 15.41/2.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f12])).
% 15.41/2.50  
% 15.41/2.50  fof(f4,axiom,(
% 15.41/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f17,plain,(
% 15.41/2.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.41/2.50    inference(ennf_transformation,[],[f4])).
% 15.41/2.50  
% 15.41/2.50  fof(f26,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f17])).
% 15.41/2.50  
% 15.41/2.50  fof(f8,axiom,(
% 15.41/2.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f18,plain,(
% 15.41/2.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.41/2.50    inference(ennf_transformation,[],[f8])).
% 15.41/2.50  
% 15.41/2.50  fof(f30,plain,(
% 15.41/2.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f18])).
% 15.41/2.50  
% 15.41/2.50  fof(f6,axiom,(
% 15.41/2.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f28,plain,(
% 15.41/2.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.41/2.50    inference(cnf_transformation,[],[f6])).
% 15.41/2.50  
% 15.41/2.50  fof(f3,axiom,(
% 15.41/2.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f15,plain,(
% 15.41/2.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.41/2.50    inference(unused_predicate_definition_removal,[],[f3])).
% 15.41/2.50  
% 15.41/2.50  fof(f16,plain,(
% 15.41/2.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 15.41/2.50    inference(ennf_transformation,[],[f15])).
% 15.41/2.50  
% 15.41/2.50  fof(f25,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f16])).
% 15.41/2.50  
% 15.41/2.50  fof(f40,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 15.41/2.50    inference(definition_unfolding,[],[f25,f32])).
% 15.41/2.50  
% 15.41/2.50  fof(f36,plain,(
% 15.41/2.50    r1_xboole_0(sK2,sK0)),
% 15.41/2.50    inference(cnf_transformation,[],[f22])).
% 15.41/2.50  
% 15.41/2.50  fof(f5,axiom,(
% 15.41/2.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.41/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f27,plain,(
% 15.41/2.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f5])).
% 15.41/2.50  
% 15.41/2.50  fof(f37,plain,(
% 15.41/2.50    r1_xboole_0(sK3,sK1)),
% 15.41/2.50    inference(cnf_transformation,[],[f22])).
% 15.41/2.50  
% 15.41/2.50  fof(f38,plain,(
% 15.41/2.50    sK1 != sK2),
% 15.41/2.50    inference(cnf_transformation,[],[f22])).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14,negated_conjecture,
% 15.41/2.50      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 15.41/2.50      inference(cnf_transformation,[],[f35]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_9,plain,
% 15.41/2.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f33]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_0,plain,
% 15.41/2.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f23]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_141,negated_conjecture,
% 15.41/2.50      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 15.41/2.50      inference(theory_normalisation,[status(thm)],[c_14,c_9,c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 15.41/2.50      inference(cnf_transformation,[],[f29]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_474,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_141,c_6]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8,plain,
% 15.41/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.41/2.50      inference(cnf_transformation,[],[f41]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_588,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_595,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_588,c_6]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7295,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK3),k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK3),k4_xboole_0(sK2,sK3))) = k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_474,c_595]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1,plain,
% 15.41/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f39]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_576,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5946,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK3),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK1,sK0),sK3))) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_474,c_576]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7345,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK1,sK0),sK3)))) = k4_xboole_0(sK2,sK3) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_7295,c_474,c_5946]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_10,plain,
% 15.41/2.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f34]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_220,plain,
% 15.41/2.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_381,plain,
% 15.41/2.50      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_0,c_220]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2134,plain,
% 15.41/2.50      ( r1_tarski(sK3,k2_xboole_0(sK1,sK0)) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_141,c_381]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3,plain,
% 15.41/2.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.41/2.50      inference(cnf_transformation,[],[f26]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_223,plain,
% 15.41/2.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2160,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2134,c_223]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2305,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2160,c_6]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_383,plain,
% 15.41/2.50      ( r1_tarski(sK2,k2_xboole_0(sK1,sK0)) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_141,c_220]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1008,plain,
% 15.41/2.50      ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_383,c_223]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1287,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1008,c_6]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2317,plain,
% 15.41/2.50      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_2305,c_1287]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7,plain,
% 15.41/2.50      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 15.41/2.50      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 15.41/2.50      inference(cnf_transformation,[],[f30]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_221,plain,
% 15.41/2.50      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 15.41/2.50      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_464,plain,
% 15.41/2.50      ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
% 15.41/2.50      | r1_tarski(k4_xboole_0(X0,sK2),sK3) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_141,c_221]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_762,plain,
% 15.41/2.50      ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_220,c_464]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1010,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK3) = sK3 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_762,c_223]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1680,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1010,c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_229,plain,
% 15.41/2.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2673,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_141,c_229]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3129,plain,
% 15.41/2.50      ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2673,c_229]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14683,plain,
% 15.41/2.50      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1680,c_3129]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1683,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k4_xboole_0(sK1,sK2)) = sK3 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1010,c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14686,plain,
% 15.41/2.50      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(light_normalisation,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_14683,c_141,c_1683,c_2160]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_24504,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK3,k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,sK3) ),
% 15.41/2.50      inference(light_normalisation,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_7345,c_2317,c_7345,c_14686]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5,plain,
% 15.41/2.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f28]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_475,plain,
% 15.41/2.50      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_476,plain,
% 15.41/2.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_475,c_5]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3115,plain,
% 15.41/2.50      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,sK2) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_476,c_2673]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3400,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK1,sK0)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_3115,c_6]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1102,plain,
% 15.41/2.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_476,c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3409,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_3115,c_1102]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3435,plain,
% 15.41/2.50      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_3400,c_1287,c_3409]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_661,plain,
% 15.41/2.50      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_141,c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_758,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_661,c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2949,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK2,sK3) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1683,c_758]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2950,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_2949,c_141]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_228,plain,
% 15.41/2.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3202,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2950,c_228]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_230,plain,
% 15.41/2.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3855,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,X0),X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2673,c_230]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14682,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1680,c_3855]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14687,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_14682,c_141,c_2160]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14961,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2)),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_14687,c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14970,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2)),X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_14687,c_230]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14760,plain,
% 15.41/2.50      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_14686,c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_15634,plain,
% 15.41/2.50      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1683,c_14760]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_15709,plain,
% 15.41/2.50      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_15634,c_14686]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_755,plain,
% 15.41/2.50      ( k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_661,c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_904,plain,
% 15.41/2.50      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) = k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(X0,X1))) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_755,c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20453,plain,
% 15.41/2.50      ( k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,X1)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_904,c_230]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1800,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(X0,sK0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_228,c_755]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3134,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK1,sK0))) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2673,c_228]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_10001,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X0,X1)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_3134,c_230]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3893,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_230,c_2673]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4813,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,X1))) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(X1,X0))) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_230,c_3893]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_10025,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(X1,X0)) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_10001,c_4813]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20647,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(X0,X1),sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(X1,X0))) ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_20453,c_1800,c_10025]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20464,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X0)))) = k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_904,c_1680]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_15665,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_14760,c_230]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20632,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X0)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_20464,c_15665]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14670,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,X1))) = k2_xboole_0(X0,k2_xboole_0(sK3,X1)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1680,c_228]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20633,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK3,X0),sK0))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_20632,c_1800,c_14670]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20657,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(X0,sK3)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_20647,c_20633]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2146,plain,
% 15.41/2.50      ( r1_tarski(k4_xboole_0(sK0,sK2),sK3) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_381,c_464]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2300,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK3) = sK3 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2146,c_223]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2503,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2300,c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3856,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK0,sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,sK3) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2300,c_230]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2,plain,
% 15.41/2.50      ( ~ r1_xboole_0(X0,X1)
% 15.41/2.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f40]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_13,negated_conjecture,
% 15.41/2.50      ( r1_xboole_0(sK2,sK0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f36]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_102,plain,
% 15.41/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 15.41/2.50      | sK0 != X1
% 15.41/2.50      | sK2 != X0 ),
% 15.41/2.50      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_103,plain,
% 15.41/2.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 15.41/2.50      inference(unflattening,[status(thm)],[c_102]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_584,plain,
% 15.41/2.50      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_103,c_8]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_597,plain,
% 15.41/2.50      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_584,c_5]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_581,plain,
% 15.41/2.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12790,plain,
% 15.41/2.50      ( k4_xboole_0(sK0,k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK0,sK2) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_597,c_581]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_590,plain,
% 15.41/2.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_103,c_8]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_591,plain,
% 15.41/2.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_590,c_103]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_592,plain,
% 15.41/2.50      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_591,c_5]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12864,plain,
% 15.41/2.50      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_12790,c_592]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12865,plain,
% 15.41/2.50      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_12864,c_5]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_15984,plain,
% 15.41/2.50      ( k2_xboole_0(sK0,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
% 15.41/2.50      inference(light_normalisation,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_2503,c_3856,c_12865]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_15995,plain,
% 15.41/2.50      ( k2_xboole_0(sK0,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_0,c_15984]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20663,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_20657,c_15995]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20664,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_20663,c_14670]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22790,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(sK1,k2_xboole_0(sK3,X0))) = k2_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
% 15.41/2.50      inference(light_normalisation,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_14961,c_14970,c_15709,c_20664]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22798,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(sK3,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK1,sK0))) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_3202,c_22790]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22909,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(sK3,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_22798,c_2160]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3194,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2950,c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_11470,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_0,c_3194]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_16041,plain,
% 15.41/2.50      ( k2_xboole_0(sK3,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK3,X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_15984,c_228]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22910,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_22909,c_11470,c_16041]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22911,plain,
% 15.41/2.50      ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,sK0) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_22910,c_1683]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_24505,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,sK3) ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_24504,c_3435,c_22911]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_24506,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(sK1,sK3),k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK3)))) = k4_xboole_0(sK2,sK3) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_24505,c_22911]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4,plain,
% 15.41/2.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f27]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_222,plain,
% 15.41/2.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_462,plain,
% 15.41/2.50      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 15.41/2.50      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_0,c_221]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4875,plain,
% 15.41/2.50      ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
% 15.41/2.50      | r1_tarski(k4_xboole_0(X0,sK3),sK2) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_141,c_462]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5438,plain,
% 15.41/2.50      ( r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_222,c_4875]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6494,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK0),X0),sK3),sK2) = sK2 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_5438,c_223]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_51840,plain,
% 15.41/2.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3),sK2) = sK2 ),
% 15.41/2.50      inference(light_normalisation,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_6494,c_6494,c_22911]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_51880,plain,
% 15.41/2.50      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK3),X0),sK3)) = sK2 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_51840,c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_52121,plain,
% 15.41/2.50      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),sK3)) = sK2 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_24506,c_51880]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12,negated_conjecture,
% 15.41/2.50      ( r1_xboole_0(sK3,sK1) ),
% 15.41/2.50      inference(cnf_transformation,[],[f37]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_97,plain,
% 15.41/2.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 15.41/2.50      | sK3 != X0
% 15.41/2.50      | sK1 != X1 ),
% 15.41/2.50      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_98,plain,
% 15.41/2.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 15.41/2.50      inference(unflattening,[status(thm)],[c_97]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_577,plain,
% 15.41/2.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1,c_98]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_850,plain,
% 15.41/2.50      ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_577,c_8]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_851,plain,
% 15.41/2.50      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_850,c_5]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_906,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_755,c_6]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_25301,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK3)),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_906,c_906,c_22911]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3903,plain,
% 15.41/2.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_230,c_6]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_25302,plain,
% 15.41/2.50      ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_25301,c_3903]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_25319,plain,
% 15.41/2.50      ( k4_xboole_0(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK2,sK3) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1683,c_25302]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_25373,plain,
% 15.41/2.50      ( k4_xboole_0(sK2,sK3) = sK1 ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_25319,c_851,c_1683]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4859,plain,
% 15.41/2.50      ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_383,c_462]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4905,plain,
% 15.41/2.50      ( r1_tarski(sK2,sK1) = iProver_top ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_4859,c_597]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_35738,plain,
% 15.41/2.50      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_4905,c_223]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_52203,plain,
% 15.41/2.50      ( sK2 = sK1 ),
% 15.41/2.50      inference(light_normalisation,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_52121,c_851,c_25373,c_35738]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_144,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_232,plain,
% 15.41/2.50      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_144]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_233,plain,
% 15.41/2.50      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_232]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_143,plain,( X0 = X0 ),theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_151,plain,
% 15.41/2.50      ( sK1 = sK1 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_143]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_11,negated_conjecture,
% 15.41/2.50      ( sK1 != sK2 ),
% 15.41/2.50      inference(cnf_transformation,[],[f38]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(contradiction,plain,
% 15.41/2.50      ( $false ),
% 15.41/2.50      inference(minisat,[status(thm)],[c_52203,c_233,c_151,c_11]) ).
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  ------                               Statistics
% 15.41/2.50  
% 15.41/2.50  ------ General
% 15.41/2.50  
% 15.41/2.50  abstr_ref_over_cycles:                  0
% 15.41/2.50  abstr_ref_under_cycles:                 0
% 15.41/2.50  gc_basic_clause_elim:                   0
% 15.41/2.50  forced_gc_time:                         0
% 15.41/2.50  parsing_time:                           0.01
% 15.41/2.50  unif_index_cands_time:                  0.
% 15.41/2.50  unif_index_add_time:                    0.
% 15.41/2.50  orderings_time:                         0.
% 15.41/2.50  out_proof_time:                         0.01
% 15.41/2.50  total_time:                             1.628
% 15.41/2.50  num_of_symbols:                         40
% 15.41/2.50  num_of_terms:                           68352
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing
% 15.41/2.50  
% 15.41/2.50  num_of_splits:                          0
% 15.41/2.50  num_of_split_atoms:                     0
% 15.41/2.50  num_of_reused_defs:                     0
% 15.41/2.50  num_eq_ax_congr_red:                    0
% 15.41/2.50  num_of_sem_filtered_clauses:            1
% 15.41/2.50  num_of_subtypes:                        0
% 15.41/2.50  monotx_restored_types:                  0
% 15.41/2.50  sat_num_of_epr_types:                   0
% 15.41/2.50  sat_num_of_non_cyclic_types:            0
% 15.41/2.50  sat_guarded_non_collapsed_types:        0
% 15.41/2.50  num_pure_diseq_elim:                    0
% 15.41/2.50  simp_replaced_by:                       0
% 15.41/2.50  res_preprocessed:                       68
% 15.41/2.50  prep_upred:                             0
% 15.41/2.50  prep_unflattend:                        4
% 15.41/2.50  smt_new_axioms:                         0
% 15.41/2.50  pred_elim_cands:                        1
% 15.41/2.50  pred_elim:                              1
% 15.41/2.50  pred_elim_cl:                           1
% 15.41/2.50  pred_elim_cycles:                       3
% 15.41/2.50  merged_defs:                            0
% 15.41/2.50  merged_defs_ncl:                        0
% 15.41/2.50  bin_hyper_res:                          0
% 15.41/2.50  prep_cycles:                            4
% 15.41/2.50  pred_elim_time:                         0.
% 15.41/2.50  splitting_time:                         0.
% 15.41/2.50  sem_filter_time:                        0.
% 15.41/2.50  monotx_time:                            0.
% 15.41/2.50  subtype_inf_time:                       0.
% 15.41/2.50  
% 15.41/2.50  ------ Problem properties
% 15.41/2.50  
% 15.41/2.50  clauses:                                14
% 15.41/2.50  conjectures:                            2
% 15.41/2.50  epr:                                    1
% 15.41/2.50  horn:                                   14
% 15.41/2.50  ground:                                 4
% 15.41/2.50  unary:                                  12
% 15.41/2.50  binary:                                 2
% 15.41/2.50  lits:                                   16
% 15.41/2.50  lits_eq:                                11
% 15.41/2.50  fd_pure:                                0
% 15.41/2.50  fd_pseudo:                              0
% 15.41/2.50  fd_cond:                                0
% 15.41/2.50  fd_pseudo_cond:                         0
% 15.41/2.50  ac_symbols:                             1
% 15.41/2.50  
% 15.41/2.50  ------ Propositional Solver
% 15.41/2.50  
% 15.41/2.50  prop_solver_calls:                      40
% 15.41/2.50  prop_fast_solver_calls:                 729
% 15.41/2.50  smt_solver_calls:                       0
% 15.41/2.50  smt_fast_solver_calls:                  0
% 15.41/2.50  prop_num_of_clauses:                    18230
% 15.41/2.50  prop_preprocess_simplified:             16068
% 15.41/2.50  prop_fo_subsumed:                       0
% 15.41/2.50  prop_solver_time:                       0.
% 15.41/2.50  smt_solver_time:                        0.
% 15.41/2.50  smt_fast_solver_time:                   0.
% 15.41/2.50  prop_fast_solver_time:                  0.
% 15.41/2.50  prop_unsat_core_time:                   0.002
% 15.41/2.50  
% 15.41/2.50  ------ QBF
% 15.41/2.50  
% 15.41/2.50  qbf_q_res:                              0
% 15.41/2.50  qbf_num_tautologies:                    0
% 15.41/2.50  qbf_prep_cycles:                        0
% 15.41/2.50  
% 15.41/2.50  ------ BMC1
% 15.41/2.50  
% 15.41/2.50  bmc1_current_bound:                     -1
% 15.41/2.50  bmc1_last_solved_bound:                 -1
% 15.41/2.50  bmc1_unsat_core_size:                   -1
% 15.41/2.50  bmc1_unsat_core_parents_size:           -1
% 15.41/2.50  bmc1_merge_next_fun:                    0
% 15.41/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.41/2.50  
% 15.41/2.50  ------ Instantiation
% 15.41/2.50  
% 15.41/2.50  inst_num_of_clauses:                    4207
% 15.41/2.50  inst_num_in_passive:                    2324
% 15.41/2.50  inst_num_in_active:                     1460
% 15.41/2.50  inst_num_in_unprocessed:                423
% 15.41/2.50  inst_num_of_loops:                      1650
% 15.41/2.50  inst_num_of_learning_restarts:          0
% 15.41/2.50  inst_num_moves_active_passive:          182
% 15.41/2.50  inst_lit_activity:                      0
% 15.41/2.50  inst_lit_activity_moves:                2
% 15.41/2.50  inst_num_tautologies:                   0
% 15.41/2.50  inst_num_prop_implied:                  0
% 15.41/2.50  inst_num_existing_simplified:           0
% 15.41/2.50  inst_num_eq_res_simplified:             0
% 15.41/2.50  inst_num_child_elim:                    0
% 15.41/2.50  inst_num_of_dismatching_blockings:      9190
% 15.41/2.50  inst_num_of_non_proper_insts:           5878
% 15.41/2.50  inst_num_of_duplicates:                 0
% 15.41/2.50  inst_inst_num_from_inst_to_res:         0
% 15.41/2.50  inst_dismatching_checking_time:         0.
% 15.41/2.50  
% 15.41/2.50  ------ Resolution
% 15.41/2.50  
% 15.41/2.50  res_num_of_clauses:                     0
% 15.41/2.50  res_num_in_passive:                     0
% 15.41/2.50  res_num_in_active:                      0
% 15.41/2.50  res_num_of_loops:                       72
% 15.41/2.50  res_forward_subset_subsumed:            1388
% 15.41/2.50  res_backward_subset_subsumed:           2
% 15.41/2.50  res_forward_subsumed:                   0
% 15.41/2.50  res_backward_subsumed:                  0
% 15.41/2.50  res_forward_subsumption_resolution:     0
% 15.41/2.50  res_backward_subsumption_resolution:    0
% 15.41/2.50  res_clause_to_clause_subsumption:       55516
% 15.41/2.50  res_orphan_elimination:                 0
% 15.41/2.50  res_tautology_del:                      554
% 15.41/2.50  res_num_eq_res_simplified:              0
% 15.41/2.50  res_num_sel_changes:                    0
% 15.41/2.50  res_moves_from_active_to_pass:          0
% 15.41/2.50  
% 15.41/2.50  ------ Superposition
% 15.41/2.50  
% 15.41/2.50  sup_time_total:                         0.
% 15.41/2.50  sup_time_generating:                    0.
% 15.41/2.50  sup_time_sim_full:                      0.
% 15.41/2.50  sup_time_sim_immed:                     0.
% 15.41/2.50  
% 15.41/2.50  sup_num_of_clauses:                     4600
% 15.41/2.50  sup_num_in_active:                      290
% 15.41/2.50  sup_num_in_passive:                     4310
% 15.41/2.50  sup_num_of_loops:                       329
% 15.41/2.50  sup_fw_superposition:                   7377
% 15.41/2.50  sup_bw_superposition:                   5967
% 15.41/2.50  sup_immediate_simplified:               6199
% 15.41/2.50  sup_given_eliminated:                   5
% 15.41/2.50  comparisons_done:                       0
% 15.41/2.50  comparisons_avoided:                    0
% 15.41/2.50  
% 15.41/2.50  ------ Simplifications
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  sim_fw_subset_subsumed:                 4
% 15.41/2.50  sim_bw_subset_subsumed:                 4
% 15.41/2.50  sim_fw_subsumed:                        906
% 15.41/2.50  sim_bw_subsumed:                        117
% 15.41/2.50  sim_fw_subsumption_res:                 0
% 15.41/2.50  sim_bw_subsumption_res:                 0
% 15.41/2.50  sim_tautology_del:                      5
% 15.41/2.50  sim_eq_tautology_del:                   629
% 15.41/2.50  sim_eq_res_simp:                        0
% 15.41/2.50  sim_fw_demodulated:                     3641
% 15.41/2.50  sim_bw_demodulated:                     165
% 15.41/2.50  sim_light_normalised:                   4055
% 15.41/2.50  sim_joinable_taut:                      232
% 15.41/2.50  sim_joinable_simp:                      0
% 15.41/2.50  sim_ac_normalised:                      0
% 15.41/2.50  sim_smt_subsumption:                    0
% 15.41/2.50  
%------------------------------------------------------------------------------
