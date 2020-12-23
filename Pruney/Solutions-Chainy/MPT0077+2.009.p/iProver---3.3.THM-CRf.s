%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:38 EST 2020

% Result     : Theorem 27.48s
% Output     : CNFRefutation 27.48s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 908 expanded)
%              Number of clauses        :   91 ( 374 expanded)
%              Number of leaves         :   14 ( 197 expanded)
%              Depth                    :   27
%              Number of atoms          :  237 (2296 expanded)
%              Number of equality atoms :  116 ( 486 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22])).

fof(f41,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f37,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_540,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_543,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2442,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) = iProver_top
    | r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_540,c_543])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_163,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X3 != X2
    | k2_xboole_0(X3,X4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_164,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_658,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | r1_xboole_0(sK0,sK2) ),
    inference(resolution,[status(thm)],[c_4,c_12])).

cnf(c_712,plain,
    ( r1_xboole_0(sK1,sK0)
    | r1_xboole_0(sK0,sK2) ),
    inference(resolution,[status(thm)],[c_164,c_658])).

cnf(c_659,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | r1_xboole_0(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_4,c_13])).

cnf(c_713,plain,
    ( r1_xboole_0(sK1,sK0)
    | r1_xboole_0(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_164,c_659])).

cnf(c_746,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_790,plain,
    ( r1_xboole_0(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_713,c_746])).

cnf(c_802,plain,
    ( r1_xboole_0(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_790,c_4])).

cnf(c_803,plain,
    ( r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_2848,plain,
    ( r1_xboole_0(sK0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2442,c_803])).

cnf(c_2853,plain,
    ( r1_xboole_0(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2848,c_543])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_545,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3431,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2853,c_545])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3967,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3431,c_7])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_853,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_787,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_958,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_787])).

cnf(c_1135,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_787,c_958])).

cnf(c_1693,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_853,c_1135])).

cnf(c_3977,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3967,c_1693])).

cnf(c_7683,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),X0),k1_xboole_0) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),X0),sK1) ),
    inference(superposition,[status(thm)],[c_3977,c_6])).

cnf(c_5,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_946,plain,
    ( k4_xboole_0(X0,X1) = X2
    | k4_xboole_0(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_10365,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) != k1_xboole_0
    | k4_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_3431,c_946])).

cnf(c_10738,plain,
    ( k4_xboole_0(sK1,sK0) = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10365,c_787])).

cnf(c_10739,plain,
    ( k4_xboole_0(sK1,sK0) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_10738])).

cnf(c_44501,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,X0),sK1) = k2_xboole_0(k2_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7683,c_10739])).

cnf(c_845,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_1512,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_0,c_845])).

cnf(c_5426,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1512,c_0])).

cnf(c_44502,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK1)) = k2_xboole_0(k2_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_44501,c_5426])).

cnf(c_44582,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_44502,c_0])).

cnf(c_1542,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_845,c_0])).

cnf(c_541,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2441,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) = iProver_top
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_543])).

cnf(c_734,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1243,plain,
    ( r1_xboole_0(sK0,sK2)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1244,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
    | r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1243])).

cnf(c_276,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_273,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2073,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_276,c_273])).

cnf(c_2230,plain,
    ( ~ r1_xboole_0(k2_xboole_0(X0,X1),X2)
    | r1_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_2073,c_0])).

cnf(c_2261,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK1),sK0)
    | r1_xboole_0(sK0,sK2) ),
    inference(resolution,[status(thm)],[c_2230,c_658])).

cnf(c_2275,plain,
    ( r1_xboole_0(sK2,sK0)
    | r1_xboole_0(sK0,sK2) ),
    inference(resolution,[status(thm)],[c_2261,c_164])).

cnf(c_1251,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | r1_xboole_0(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2362,plain,
    ( r1_xboole_0(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2275,c_1251])).

cnf(c_2754,plain,
    ( r1_xboole_0(sK0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2441,c_734,c_1244,c_1251,c_2275])).

cnf(c_3427,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2754,c_545])).

cnf(c_10362,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)) != k1_xboole_0
    | k4_xboole_0(sK0,sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_3427,c_946])).

cnf(c_10748,plain,
    ( k4_xboole_0(sK0,sK2) = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10362,c_787])).

cnf(c_10749,plain,
    ( k4_xboole_0(sK0,sK2) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10748])).

cnf(c_11652,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_10749,c_7])).

cnf(c_12285,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_11652])).

cnf(c_12552,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_1542,c_12285])).

cnf(c_12604,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_12552,c_11652])).

cnf(c_113618,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_44582,c_12604])).

cnf(c_3430,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2848,c_545])).

cnf(c_10363,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) != k1_xboole_0
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_3430,c_946])).

cnf(c_10743,plain,
    ( k4_xboole_0(sK0,sK1) = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10363,c_787])).

cnf(c_10744,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10743])).

cnf(c_113824,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_113618,c_10744])).

cnf(c_546,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_114507,plain,
    ( k4_xboole_0(sK0,sK0) != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_113824,c_546])).

cnf(c_11118,plain,
    ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10744,c_3430])).

cnf(c_114558,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_114507,c_11118])).

cnf(c_114559,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_114558])).

cnf(c_114619,plain,
    ( r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_114559,c_543])).

cnf(c_538,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164])).

cnf(c_1555,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k2_xboole_0(X2,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_538])).

cnf(c_114942,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_114619,c_1555])).

cnf(c_882,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_717,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_721,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k1_xboole_0
    | r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_718,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_17,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_114942,c_2362,c_882,c_802,c_721,c_718,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:50:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.48/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.48/3.99  
% 27.48/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.48/3.99  
% 27.48/3.99  ------  iProver source info
% 27.48/3.99  
% 27.48/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.48/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.48/3.99  git: non_committed_changes: false
% 27.48/3.99  git: last_make_outside_of_git: false
% 27.48/3.99  
% 27.48/3.99  ------ 
% 27.48/3.99  ------ Parsing...
% 27.48/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.48/3.99  
% 27.48/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.48/3.99  
% 27.48/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.48/3.99  
% 27.48/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.48/3.99  ------ Proving...
% 27.48/3.99  ------ Problem Properties 
% 27.48/3.99  
% 27.48/3.99  
% 27.48/3.99  clauses                                 14
% 27.48/3.99  conjectures                             3
% 27.48/3.99  EPR                                     3
% 27.48/3.99  Horn                                    12
% 27.48/3.99  unary                                   5
% 27.48/3.99  binary                                  7
% 27.48/3.99  lits                                    25
% 27.48/3.99  lits eq                                 9
% 27.48/3.99  fd_pure                                 0
% 27.48/3.99  fd_pseudo                               0
% 27.48/3.99  fd_cond                                 0
% 27.48/3.99  fd_pseudo_cond                          2
% 27.48/3.99  AC symbols                              0
% 27.48/3.99  
% 27.48/3.99  ------ Input Options Time Limit: Unbounded
% 27.48/3.99  
% 27.48/3.99  
% 27.48/3.99  ------ 
% 27.48/3.99  Current options:
% 27.48/3.99  ------ 
% 27.48/3.99  
% 27.48/3.99  
% 27.48/3.99  
% 27.48/3.99  
% 27.48/3.99  ------ Proving...
% 27.48/3.99  
% 27.48/3.99  
% 27.48/3.99  % SZS status Theorem for theBenchmark.p
% 27.48/3.99  
% 27.48/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.48/3.99  
% 27.48/3.99  fof(f13,conjecture,(
% 27.48/3.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f14,negated_conjecture,(
% 27.48/3.99    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 27.48/3.99    inference(negated_conjecture,[],[f13])).
% 27.48/3.99  
% 27.48/3.99  fof(f20,plain,(
% 27.48/3.99    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 27.48/3.99    inference(ennf_transformation,[],[f14])).
% 27.48/3.99  
% 27.48/3.99  fof(f22,plain,(
% 27.48/3.99    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 27.48/3.99    introduced(choice_axiom,[])).
% 27.48/3.99  
% 27.48/3.99  fof(f23,plain,(
% 27.48/3.99    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 27.48/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22])).
% 27.48/3.99  
% 27.48/3.99  fof(f41,plain,(
% 27.48/3.99    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 27.48/3.99    inference(cnf_transformation,[],[f23])).
% 27.48/3.99  
% 27.48/3.99  fof(f4,axiom,(
% 27.48/3.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f15,plain,(
% 27.48/3.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 27.48/3.99    inference(ennf_transformation,[],[f4])).
% 27.48/3.99  
% 27.48/3.99  fof(f28,plain,(
% 27.48/3.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 27.48/3.99    inference(cnf_transformation,[],[f15])).
% 27.48/3.99  
% 27.48/3.99  fof(f10,axiom,(
% 27.48/3.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f17,plain,(
% 27.48/3.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 27.48/3.99    inference(ennf_transformation,[],[f10])).
% 27.48/3.99  
% 27.48/3.99  fof(f18,plain,(
% 27.48/3.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 27.48/3.99    inference(flattening,[],[f17])).
% 27.48/3.99  
% 27.48/3.99  fof(f34,plain,(
% 27.48/3.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 27.48/3.99    inference(cnf_transformation,[],[f18])).
% 27.48/3.99  
% 27.48/3.99  fof(f11,axiom,(
% 27.48/3.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f35,plain,(
% 27.48/3.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.48/3.99    inference(cnf_transformation,[],[f11])).
% 27.48/3.99  
% 27.48/3.99  fof(f42,plain,(
% 27.48/3.99    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 27.48/3.99    inference(cnf_transformation,[],[f23])).
% 27.48/3.99  
% 27.48/3.99  fof(f2,axiom,(
% 27.48/3.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f21,plain,(
% 27.48/3.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 27.48/3.99    inference(nnf_transformation,[],[f2])).
% 27.48/3.99  
% 27.48/3.99  fof(f25,plain,(
% 27.48/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 27.48/3.99    inference(cnf_transformation,[],[f21])).
% 27.48/3.99  
% 27.48/3.99  fof(f9,axiom,(
% 27.48/3.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f33,plain,(
% 27.48/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.48/3.99    inference(cnf_transformation,[],[f9])).
% 27.48/3.99  
% 27.48/3.99  fof(f44,plain,(
% 27.48/3.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 27.48/3.99    inference(definition_unfolding,[],[f25,f33])).
% 27.48/3.99  
% 27.48/3.99  fof(f7,axiom,(
% 27.48/3.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f31,plain,(
% 27.48/3.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 27.48/3.99    inference(cnf_transformation,[],[f7])).
% 27.48/3.99  
% 27.48/3.99  fof(f8,axiom,(
% 27.48/3.99    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f32,plain,(
% 27.48/3.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 27.48/3.99    inference(cnf_transformation,[],[f8])).
% 27.48/3.99  
% 27.48/3.99  fof(f1,axiom,(
% 27.48/3.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f24,plain,(
% 27.48/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.48/3.99    inference(cnf_transformation,[],[f1])).
% 27.48/3.99  
% 27.48/3.99  fof(f6,axiom,(
% 27.48/3.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f30,plain,(
% 27.48/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 27.48/3.99    inference(cnf_transformation,[],[f6])).
% 27.48/3.99  
% 27.48/3.99  fof(f5,axiom,(
% 27.48/3.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 27.48/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.48/3.99  
% 27.48/3.99  fof(f16,plain,(
% 27.48/3.99    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 27.48/3.99    inference(ennf_transformation,[],[f5])).
% 27.48/3.99  
% 27.48/3.99  fof(f29,plain,(
% 27.48/3.99    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 27.48/3.99    inference(cnf_transformation,[],[f16])).
% 27.48/3.99  
% 27.48/3.99  fof(f26,plain,(
% 27.48/3.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.48/3.99    inference(cnf_transformation,[],[f21])).
% 27.48/3.99  
% 27.48/3.99  fof(f43,plain,(
% 27.48/3.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.48/3.99    inference(definition_unfolding,[],[f26,f33])).
% 27.48/3.99  
% 27.48/3.99  fof(f37,plain,(
% 27.48/3.99    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 27.48/3.99    inference(cnf_transformation,[],[f23])).
% 27.48/3.99  
% 27.48/3.99  cnf(c_13,negated_conjecture,
% 27.48/3.99      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1) ),
% 27.48/3.99      inference(cnf_transformation,[],[f41]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_540,plain,
% 27.48/3.99      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
% 27.48/3.99      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 27.48/3.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_4,plain,
% 27.48/3.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 27.48/3.99      inference(cnf_transformation,[],[f28]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_543,plain,
% 27.48/3.99      ( r1_xboole_0(X0,X1) != iProver_top
% 27.48/3.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 27.48/3.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2442,plain,
% 27.48/3.99      ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) = iProver_top
% 27.48/3.99      | r1_xboole_0(sK0,sK1) = iProver_top ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_540,c_543]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_9,plain,
% 27.48/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 27.48/3.99      inference(cnf_transformation,[],[f34]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10,plain,
% 27.48/3.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.48/3.99      inference(cnf_transformation,[],[f35]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_163,plain,
% 27.48/3.99      ( ~ r1_xboole_0(X0,X1)
% 27.48/3.99      | r1_xboole_0(X2,X1)
% 27.48/3.99      | X3 != X2
% 27.48/3.99      | k2_xboole_0(X3,X4) != X0 ),
% 27.48/3.99      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_164,plain,
% 27.48/3.99      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 27.48/3.99      inference(unflattening,[status(thm)],[c_163]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_12,negated_conjecture,
% 27.48/3.99      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2) ),
% 27.48/3.99      inference(cnf_transformation,[],[f42]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_658,plain,
% 27.48/3.99      ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | r1_xboole_0(sK0,sK2) ),
% 27.48/3.99      inference(resolution,[status(thm)],[c_4,c_12]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_712,plain,
% 27.48/3.99      ( r1_xboole_0(sK1,sK0) | r1_xboole_0(sK0,sK2) ),
% 27.48/3.99      inference(resolution,[status(thm)],[c_164,c_658]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_659,plain,
% 27.48/3.99      ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | r1_xboole_0(sK0,sK1) ),
% 27.48/3.99      inference(resolution,[status(thm)],[c_4,c_13]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_713,plain,
% 27.48/3.99      ( r1_xboole_0(sK1,sK0) | r1_xboole_0(sK0,sK1) ),
% 27.48/3.99      inference(resolution,[status(thm)],[c_164,c_659]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_746,plain,
% 27.48/3.99      ( r1_xboole_0(sK1,sK0) | ~ r1_xboole_0(sK0,sK1) ),
% 27.48/3.99      inference(instantiation,[status(thm)],[c_4]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_790,plain,
% 27.48/3.99      ( r1_xboole_0(sK1,sK0) ),
% 27.48/3.99      inference(global_propositional_subsumption,
% 27.48/3.99                [status(thm)],
% 27.48/3.99                [c_712,c_713,c_746]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_802,plain,
% 27.48/3.99      ( r1_xboole_0(sK0,sK1) ),
% 27.48/3.99      inference(resolution,[status(thm)],[c_790,c_4]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_803,plain,
% 27.48/3.99      ( r1_xboole_0(sK0,sK1) = iProver_top ),
% 27.48/3.99      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2848,plain,
% 27.48/3.99      ( r1_xboole_0(sK0,sK1) = iProver_top ),
% 27.48/3.99      inference(global_propositional_subsumption,
% 27.48/3.99                [status(thm)],
% 27.48/3.99                [c_2442,c_803]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2853,plain,
% 27.48/3.99      ( r1_xboole_0(sK1,sK0) = iProver_top ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_2848,c_543]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2,plain,
% 27.48/3.99      ( ~ r1_xboole_0(X0,X1)
% 27.48/3.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.48/3.99      inference(cnf_transformation,[],[f44]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_545,plain,
% 27.48/3.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 27.48/3.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 27.48/3.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_3431,plain,
% 27.48/3.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_2853,c_545]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_7,plain,
% 27.48/3.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.48/3.99      inference(cnf_transformation,[],[f31]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_3967,plain,
% 27.48/3.99      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_3431,c_7]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_8,plain,
% 27.48/3.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.48/3.99      inference(cnf_transformation,[],[f32]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_853,plain,
% 27.48/3.99      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_0,plain,
% 27.48/3.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.48/3.99      inference(cnf_transformation,[],[f24]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_787,plain,
% 27.48/3.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_6,plain,
% 27.48/3.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 27.48/3.99      inference(cnf_transformation,[],[f30]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_958,plain,
% 27.48/3.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_6,c_787]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_1135,plain,
% 27.48/3.99      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_787,c_958]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_1693,plain,
% 27.48/3.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_853,c_1135]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_3977,plain,
% 27.48/3.99      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),X0)) = k1_xboole_0 ),
% 27.48/3.99      inference(light_normalisation,[status(thm)],[c_3967,c_1693]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_7683,plain,
% 27.48/3.99      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),X0),k1_xboole_0) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),X0),sK1) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_3977,c_6]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_5,plain,
% 27.48/3.99      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 27.48/3.99      inference(cnf_transformation,[],[f29]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_946,plain,
% 27.48/3.99      ( k4_xboole_0(X0,X1) = X2
% 27.48/3.99      | k4_xboole_0(X2,k4_xboole_0(X0,X1)) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10365,plain,
% 27.48/3.99      ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) != k1_xboole_0
% 27.48/3.99      | k4_xboole_0(sK1,sK0) = sK1 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_3431,c_946]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10738,plain,
% 27.48/3.99      ( k4_xboole_0(sK1,sK0) = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 27.48/3.99      inference(demodulation,[status(thm)],[c_10365,c_787]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10739,plain,
% 27.48/3.99      ( k4_xboole_0(sK1,sK0) = sK1 ),
% 27.48/3.99      inference(equality_resolution_simp,[status(thm)],[c_10738]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_44501,plain,
% 27.48/3.99      ( k2_xboole_0(k2_xboole_0(sK1,X0),sK1) = k2_xboole_0(k2_xboole_0(sK1,X0),k1_xboole_0) ),
% 27.48/3.99      inference(light_normalisation,[status(thm)],[c_7683,c_10739]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_845,plain,
% 27.48/3.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_1512,plain,
% 27.48/3.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_0,c_845]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_5426,plain,
% 27.48/3.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_1512,c_0]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_44502,plain,
% 27.48/3.99      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK1)) = k2_xboole_0(k2_xboole_0(sK1,X0),k1_xboole_0) ),
% 27.48/3.99      inference(demodulation,[status(thm)],[c_44501,c_5426]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_44582,plain,
% 27.48/3.99      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK1)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0)) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_44502,c_0]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_1542,plain,
% 27.48/3.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_845,c_0]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_541,plain,
% 27.48/3.99      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = iProver_top
% 27.48/3.99      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 27.48/3.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2441,plain,
% 27.48/3.99      ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) = iProver_top
% 27.48/3.99      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_541,c_543]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_734,plain,
% 27.48/3.99      ( ~ r1_xboole_0(sK0,sK2)
% 27.48/3.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 27.48/3.99      inference(instantiation,[status(thm)],[c_2]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_1,plain,
% 27.48/3.99      ( r1_xboole_0(X0,X1)
% 27.48/3.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 27.48/3.99      inference(cnf_transformation,[],[f43]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_1243,plain,
% 27.48/3.99      ( r1_xboole_0(sK0,sK2)
% 27.48/3.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
% 27.48/3.99      inference(instantiation,[status(thm)],[c_1]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_1244,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k1_xboole_0
% 27.48/3.99      | r1_xboole_0(sK0,sK2) = iProver_top ),
% 27.48/3.99      inference(predicate_to_equality,[status(thm)],[c_1243]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_276,plain,
% 27.48/3.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.48/3.99      theory(equality) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_273,plain,( X0 = X0 ),theory(equality) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2073,plain,
% 27.48/3.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 27.48/3.99      inference(resolution,[status(thm)],[c_276,c_273]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2230,plain,
% 27.48/3.99      ( ~ r1_xboole_0(k2_xboole_0(X0,X1),X2)
% 27.48/3.99      | r1_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 27.48/3.99      inference(resolution,[status(thm)],[c_2073,c_0]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2261,plain,
% 27.48/3.99      ( r1_xboole_0(k2_xboole_0(sK2,sK1),sK0) | r1_xboole_0(sK0,sK2) ),
% 27.48/3.99      inference(resolution,[status(thm)],[c_2230,c_658]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2275,plain,
% 27.48/3.99      ( r1_xboole_0(sK2,sK0) | r1_xboole_0(sK0,sK2) ),
% 27.48/3.99      inference(resolution,[status(thm)],[c_2261,c_164]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_1251,plain,
% 27.48/3.99      ( ~ r1_xboole_0(sK2,sK0) | r1_xboole_0(sK0,sK2) ),
% 27.48/3.99      inference(instantiation,[status(thm)],[c_4]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2362,plain,
% 27.48/3.99      ( r1_xboole_0(sK0,sK2) ),
% 27.48/3.99      inference(global_propositional_subsumption,
% 27.48/3.99                [status(thm)],
% 27.48/3.99                [c_2275,c_1251]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_2754,plain,
% 27.48/3.99      ( r1_xboole_0(sK0,sK2) = iProver_top ),
% 27.48/3.99      inference(global_propositional_subsumption,
% 27.48/3.99                [status(thm)],
% 27.48/3.99                [c_2441,c_734,c_1244,c_1251,c_2275]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_3427,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k1_xboole_0 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_2754,c_545]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10362,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK0)) != k1_xboole_0
% 27.48/3.99      | k4_xboole_0(sK0,sK2) = sK0 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_3427,c_946]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10748,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,sK2) = sK0 | k1_xboole_0 != k1_xboole_0 ),
% 27.48/3.99      inference(demodulation,[status(thm)],[c_10362,c_787]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10749,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,sK2) = sK0 ),
% 27.48/3.99      inference(equality_resolution_simp,[status(thm)],[c_10748]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_11652,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_10749,c_7]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_12285,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK0,X0) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_0,c_11652]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_12552,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_1542,c_12285]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_12604,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X0))) = k4_xboole_0(sK0,X0) ),
% 27.48/3.99      inference(light_normalisation,[status(thm)],[c_12552,c_11652]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_113618,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK1) ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_44582,c_12604]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_3430,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_2848,c_545]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10363,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) != k1_xboole_0
% 27.48/3.99      | k4_xboole_0(sK0,sK1) = sK0 ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_3430,c_946]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10743,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,sK1) = sK0 | k1_xboole_0 != k1_xboole_0 ),
% 27.48/3.99      inference(demodulation,[status(thm)],[c_10363,c_787]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_10744,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 27.48/3.99      inference(equality_resolution_simp,[status(thm)],[c_10743]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_113824,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = sK0 ),
% 27.48/3.99      inference(light_normalisation,[status(thm)],[c_113618,c_10744]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_546,plain,
% 27.48/3.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 27.48/3.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 27.48/3.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_114507,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,sK0) != k1_xboole_0
% 27.48/3.99      | r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = iProver_top ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_113824,c_546]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_11118,plain,
% 27.48/3.99      ( k4_xboole_0(sK0,sK0) = k1_xboole_0 ),
% 27.48/3.99      inference(demodulation,[status(thm)],[c_10744,c_3430]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_114558,plain,
% 27.48/3.99      ( k1_xboole_0 != k1_xboole_0
% 27.48/3.99      | r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = iProver_top ),
% 27.48/3.99      inference(light_normalisation,[status(thm)],[c_114507,c_11118]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_114559,plain,
% 27.48/3.99      ( r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))) = iProver_top ),
% 27.48/3.99      inference(equality_resolution_simp,[status(thm)],[c_114558]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_114619,plain,
% 27.48/3.99      ( r1_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)),sK0) = iProver_top ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_114559,c_543]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_538,plain,
% 27.48/3.99      ( r1_xboole_0(X0,X1) = iProver_top
% 27.48/3.99      | r1_xboole_0(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 27.48/3.99      inference(predicate_to_equality,[status(thm)],[c_164]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_1555,plain,
% 27.48/3.99      ( r1_xboole_0(X0,X1) = iProver_top
% 27.48/3.99      | r1_xboole_0(k2_xboole_0(X2,X0),X1) != iProver_top ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_0,c_538]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_114942,plain,
% 27.48/3.99      ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) = iProver_top ),
% 27.48/3.99      inference(superposition,[status(thm)],[c_114619,c_1555]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_882,plain,
% 27.48/3.99      ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
% 27.48/3.99      | k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)) != k1_xboole_0 ),
% 27.48/3.99      inference(instantiation,[status(thm)],[c_1]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_717,plain,
% 27.48/3.99      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
% 27.48/3.99      | k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k1_xboole_0 ),
% 27.48/3.99      inference(instantiation,[status(thm)],[c_2]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_721,plain,
% 27.48/3.99      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)) = k1_xboole_0
% 27.48/3.99      | r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) != iProver_top ),
% 27.48/3.99      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_718,plain,
% 27.48/3.99      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
% 27.48/3.99      | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.48/3.99      inference(instantiation,[status(thm)],[c_4]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(c_17,negated_conjecture,
% 27.48/3.99      ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
% 27.48/3.99      | ~ r1_xboole_0(sK0,sK2)
% 27.48/3.99      | ~ r1_xboole_0(sK0,sK1) ),
% 27.48/3.99      inference(cnf_transformation,[],[f37]) ).
% 27.48/3.99  
% 27.48/3.99  cnf(contradiction,plain,
% 27.48/3.99      ( $false ),
% 27.48/3.99      inference(minisat,
% 27.48/3.99                [status(thm)],
% 27.48/3.99                [c_114942,c_2362,c_882,c_802,c_721,c_718,c_17]) ).
% 27.48/3.99  
% 27.48/3.99  
% 27.48/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.48/3.99  
% 27.48/3.99  ------                               Statistics
% 27.48/3.99  
% 27.48/3.99  ------ Selected
% 27.48/3.99  
% 27.48/3.99  total_time:                             3.131
% 27.48/3.99  
%------------------------------------------------------------------------------
