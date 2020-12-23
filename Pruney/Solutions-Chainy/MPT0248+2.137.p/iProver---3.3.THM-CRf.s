%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:30 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  141 (7136 expanded)
%              Number of clauses        :   82 (2903 expanded)
%              Number of leaves         :   20 (1882 expanded)
%              Depth                    :   25
%              Number of atoms          :  249 (8179 expanded)
%              Number of equality atoms :  212 (8006 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK2
        | k1_tarski(sK0) != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_xboole_0 != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_tarski(sK0) != sK1 )
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( k1_xboole_0 != sK2
      | k1_tarski(sK0) != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_xboole_0 != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_tarski(sK0) != sK1 )
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).

fof(f43,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f63,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f43,f51,f53])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f51])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f39,f53,f53])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f26,f52])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,
    ( k1_xboole_0 != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,
    ( k1_xboole_0 != sK2
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f44,plain,
    ( k1_tarski(sK0) != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f44,f53,f53])).

fof(f45,plain,
    ( k1_tarski(sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f51])).

cnf(c_13,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_279,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2219,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_279])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_276,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2318,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2219,c_276])).

cnf(c_1,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_281,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_476,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_636,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_476,c_5])).

cnf(c_796,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(light_normalisation,[status(thm)],[c_636,c_5])).

cnf(c_630,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_476])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_644,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_630,c_3])).

cnf(c_797,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(demodulation,[status(thm)],[c_796,c_644])).

cnf(c_645,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_644,c_476])).

cnf(c_1218,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_797,c_645])).

cnf(c_1220,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_797,c_797])).

cnf(c_1226,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1220])).

cnf(c_1349,plain,
    ( sP0_iProver_split(X0,X1) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1218,c_1226])).

cnf(c_2798,plain,
    ( r1_tarski(k5_xboole_0(sP0_iProver_split(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_281,c_1349])).

cnf(c_2799,plain,
    ( r1_tarski(sP0_iProver_split(sP0_iProver_split(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2798,c_1349])).

cnf(c_478,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_878,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_478,c_645])).

cnf(c_886,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_878,c_3])).

cnf(c_898,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_886,c_5])).

cnf(c_1526,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,X0),X2)) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_898,c_1349])).

cnf(c_1527,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,X0),X2)) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_1526,c_1349])).

cnf(c_892,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_5,c_886])).

cnf(c_1407,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,X0))) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_892,c_1349])).

cnf(c_1408,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,X0))) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_1407,c_1349])).

cnf(c_1536,plain,
    ( sP0_iProver_split(sP0_iProver_split(X0,X1),X2) = sP0_iProver_split(X0,sP0_iProver_split(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1527,c_1408])).

cnf(c_2800,plain,
    ( r1_tarski(sP0_iProver_split(X0,sP0_iProver_split(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2799,c_1536])).

cnf(c_2814,plain,
    ( r1_tarski(sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_2800])).

cnf(c_3180,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sP0_iProver_split(sK1,sP0_iProver_split(sK1,sK2)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2318,c_2814])).

cnf(c_1215,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_886,c_797])).

cnf(c_1357,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X2,X1) ),
    inference(demodulation,[status(thm)],[c_1215,c_1349])).

cnf(c_1358,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,X2))) = sP0_iProver_split(X2,X1) ),
    inference(demodulation,[status(thm)],[c_1357,c_1349])).

cnf(c_895,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_645,c_886])).

cnf(c_1217,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X0)))) = X2 ),
    inference(superposition,[status(thm)],[c_797,c_895])).

cnf(c_1354,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,k5_xboole_0(X1,X0)))) = X2 ),
    inference(demodulation,[status(thm)],[c_1217,c_1349])).

cnf(c_1355,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,k5_xboole_0(X1,X0)))) = X2 ),
    inference(demodulation,[status(thm)],[c_1354,c_1349])).

cnf(c_1356,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,X0)))) = X2 ),
    inference(demodulation,[status(thm)],[c_1355,c_1349])).

cnf(c_1359,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1358,c_1356])).

cnf(c_3182,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3180,c_1359])).

cnf(c_10,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2326,plain,
    ( sK1 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2318,c_10])).

cnf(c_2322,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2318,c_276])).

cnf(c_3181,plain,
    ( sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2814,c_2322])).

cnf(c_3421,plain,
    ( sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_2814])).

cnf(c_12,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2324,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2318,c_12])).

cnf(c_11,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_296,plain,
    ( ~ r1_tarski(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_298,plain,
    ( ~ r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_296])).

cnf(c_159,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_375,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_422,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | X0 != X2
    | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_650,plain,
    ( r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | X0 != sK1
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_772,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_514,plain,
    ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_932,plain,
    ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_2412,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2324,c_13,c_12,c_11,c_298,c_375,c_772,c_932])).

cnf(c_3399,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sP0_iProver_split(sK1,sP0_iProver_split(sK1,sK2))
    | sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2318,c_3181])).

cnf(c_3429,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2
    | sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3399,c_1359])).

cnf(c_3536,plain,
    ( sK1 = k1_xboole_0
    | sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3421,c_13,c_12,c_11,c_298,c_375,c_772,c_932,c_3429])).

cnf(c_3537,plain,
    ( sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3536])).

cnf(c_3540,plain,
    ( sP0_iProver_split(sK1,sP0_iProver_split(sK1,sK2)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2318,c_3537])).

cnf(c_3576,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3540,c_1359])).

cnf(c_3671,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3182,c_2326,c_3576])).

cnf(c_3683,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_3671,c_13])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_280,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_282,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3186,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_280,c_282])).

cnf(c_3685,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_3683,c_3186])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3685,c_2412])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.52/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/0.99  
% 3.52/0.99  ------  iProver source info
% 3.52/0.99  
% 3.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/0.99  git: non_committed_changes: false
% 3.52/0.99  git: last_make_outside_of_git: false
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options
% 3.52/0.99  
% 3.52/0.99  --out_options                           all
% 3.52/0.99  --tptp_safe_out                         true
% 3.52/0.99  --problem_path                          ""
% 3.52/0.99  --include_path                          ""
% 3.52/0.99  --clausifier                            res/vclausify_rel
% 3.52/0.99  --clausifier_options                    ""
% 3.52/0.99  --stdin                                 false
% 3.52/0.99  --stats_out                             all
% 3.52/0.99  
% 3.52/0.99  ------ General Options
% 3.52/0.99  
% 3.52/0.99  --fof                                   false
% 3.52/0.99  --time_out_real                         305.
% 3.52/0.99  --time_out_virtual                      -1.
% 3.52/0.99  --symbol_type_check                     false
% 3.52/0.99  --clausify_out                          false
% 3.52/0.99  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing Options
% 3.52/0.99  
% 3.52/0.99  --preprocessing_flag                    true
% 3.52/0.99  --time_out_prep_mult                    0.1
% 3.52/0.99  --splitting_mode                        input
% 3.52/0.99  --splitting_grd                         true
% 3.52/0.99  --splitting_cvd                         false
% 3.52/0.99  --splitting_cvd_svl                     false
% 3.52/0.99  --splitting_nvd                         32
% 3.52/0.99  --sub_typing                            true
% 3.52/0.99  --prep_gs_sim                           true
% 3.52/0.99  --prep_unflatten                        true
% 3.52/0.99  --prep_res_sim                          true
% 3.52/0.99  --prep_upred                            true
% 3.52/0.99  --prep_sem_filter                       exhaustive
% 3.52/0.99  --prep_sem_filter_out                   false
% 3.52/0.99  --pred_elim                             true
% 3.52/0.99  --res_sim_input                         true
% 3.52/0.99  --eq_ax_congr_red                       true
% 3.52/0.99  --pure_diseq_elim                       true
% 3.52/0.99  --brand_transform                       false
% 3.52/0.99  --non_eq_to_eq                          false
% 3.52/0.99  --prep_def_merge                        true
% 3.52/0.99  --prep_def_merge_prop_impl              false
% 3.52/0.99  --prep_def_merge_mbd                    true
% 3.52/0.99  --prep_def_merge_tr_red                 false
% 3.52/0.99  --prep_def_merge_tr_cl                  false
% 3.52/0.99  --smt_preprocessing                     true
% 3.52/0.99  --smt_ac_axioms                         fast
% 3.52/0.99  --preprocessed_out                      false
% 3.52/0.99  --preprocessed_stats                    false
% 3.52/0.99  
% 3.52/0.99  ------ Abstraction refinement Options
% 3.52/0.99  
% 3.52/0.99  --abstr_ref                             []
% 3.52/0.99  --abstr_ref_prep                        false
% 3.52/0.99  --abstr_ref_until_sat                   false
% 3.52/0.99  --abstr_ref_sig_restrict                funpre
% 3.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.99  --abstr_ref_under                       []
% 3.52/0.99  
% 3.52/0.99  ------ SAT Options
% 3.52/0.99  
% 3.52/0.99  --sat_mode                              false
% 3.52/0.99  --sat_fm_restart_options                ""
% 3.52/0.99  --sat_gr_def                            false
% 3.52/0.99  --sat_epr_types                         true
% 3.52/0.99  --sat_non_cyclic_types                  false
% 3.52/0.99  --sat_finite_models                     false
% 3.52/0.99  --sat_fm_lemmas                         false
% 3.52/0.99  --sat_fm_prep                           false
% 3.52/0.99  --sat_fm_uc_incr                        true
% 3.52/0.99  --sat_out_model                         small
% 3.52/0.99  --sat_out_clauses                       false
% 3.52/0.99  
% 3.52/0.99  ------ QBF Options
% 3.52/0.99  
% 3.52/0.99  --qbf_mode                              false
% 3.52/0.99  --qbf_elim_univ                         false
% 3.52/0.99  --qbf_dom_inst                          none
% 3.52/0.99  --qbf_dom_pre_inst                      false
% 3.52/0.99  --qbf_sk_in                             false
% 3.52/0.99  --qbf_pred_elim                         true
% 3.52/0.99  --qbf_split                             512
% 3.52/0.99  
% 3.52/0.99  ------ BMC1 Options
% 3.52/0.99  
% 3.52/0.99  --bmc1_incremental                      false
% 3.52/0.99  --bmc1_axioms                           reachable_all
% 3.52/0.99  --bmc1_min_bound                        0
% 3.52/0.99  --bmc1_max_bound                        -1
% 3.52/0.99  --bmc1_max_bound_default                -1
% 3.52/0.99  --bmc1_symbol_reachability              true
% 3.52/0.99  --bmc1_property_lemmas                  false
% 3.52/0.99  --bmc1_k_induction                      false
% 3.52/0.99  --bmc1_non_equiv_states                 false
% 3.52/0.99  --bmc1_deadlock                         false
% 3.52/0.99  --bmc1_ucm                              false
% 3.52/0.99  --bmc1_add_unsat_core                   none
% 3.52/0.99  --bmc1_unsat_core_children              false
% 3.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.99  --bmc1_out_stat                         full
% 3.52/0.99  --bmc1_ground_init                      false
% 3.52/0.99  --bmc1_pre_inst_next_state              false
% 3.52/0.99  --bmc1_pre_inst_state                   false
% 3.52/0.99  --bmc1_pre_inst_reach_state             false
% 3.52/0.99  --bmc1_out_unsat_core                   false
% 3.52/0.99  --bmc1_aig_witness_out                  false
% 3.52/0.99  --bmc1_verbose                          false
% 3.52/0.99  --bmc1_dump_clauses_tptp                false
% 3.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.99  --bmc1_dump_file                        -
% 3.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.99  --bmc1_ucm_extend_mode                  1
% 3.52/0.99  --bmc1_ucm_init_mode                    2
% 3.52/0.99  --bmc1_ucm_cone_mode                    none
% 3.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.99  --bmc1_ucm_relax_model                  4
% 3.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.99  --bmc1_ucm_layered_model                none
% 3.52/0.99  --bmc1_ucm_max_lemma_size               10
% 3.52/0.99  
% 3.52/0.99  ------ AIG Options
% 3.52/0.99  
% 3.52/0.99  --aig_mode                              false
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation Options
% 3.52/0.99  
% 3.52/0.99  --instantiation_flag                    true
% 3.52/0.99  --inst_sos_flag                         true
% 3.52/0.99  --inst_sos_phase                        true
% 3.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel_side                     num_symb
% 3.52/0.99  --inst_solver_per_active                1400
% 3.52/0.99  --inst_solver_calls_frac                1.
% 3.52/0.99  --inst_passive_queue_type               priority_queues
% 3.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.99  --inst_passive_queues_freq              [25;2]
% 3.52/0.99  --inst_dismatching                      true
% 3.52/0.99  --inst_eager_unprocessed_to_passive     true
% 3.52/0.99  --inst_prop_sim_given                   true
% 3.52/0.99  --inst_prop_sim_new                     false
% 3.52/0.99  --inst_subs_new                         false
% 3.52/0.99  --inst_eq_res_simp                      false
% 3.52/0.99  --inst_subs_given                       false
% 3.52/0.99  --inst_orphan_elimination               true
% 3.52/0.99  --inst_learning_loop_flag               true
% 3.52/0.99  --inst_learning_start                   3000
% 3.52/0.99  --inst_learning_factor                  2
% 3.52/0.99  --inst_start_prop_sim_after_learn       3
% 3.52/0.99  --inst_sel_renew                        solver
% 3.52/0.99  --inst_lit_activity_flag                true
% 3.52/0.99  --inst_restr_to_given                   false
% 3.52/0.99  --inst_activity_threshold               500
% 3.52/0.99  --inst_out_proof                        true
% 3.52/0.99  
% 3.52/0.99  ------ Resolution Options
% 3.52/0.99  
% 3.52/0.99  --resolution_flag                       true
% 3.52/0.99  --res_lit_sel                           adaptive
% 3.52/0.99  --res_lit_sel_side                      none
% 3.52/0.99  --res_ordering                          kbo
% 3.52/0.99  --res_to_prop_solver                    active
% 3.52/0.99  --res_prop_simpl_new                    false
% 3.52/0.99  --res_prop_simpl_given                  true
% 3.52/0.99  --res_passive_queue_type                priority_queues
% 3.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.99  --res_passive_queues_freq               [15;5]
% 3.52/0.99  --res_forward_subs                      full
% 3.52/0.99  --res_backward_subs                     full
% 3.52/0.99  --res_forward_subs_resolution           true
% 3.52/0.99  --res_backward_subs_resolution          true
% 3.52/0.99  --res_orphan_elimination                true
% 3.52/0.99  --res_time_limit                        2.
% 3.52/0.99  --res_out_proof                         true
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Options
% 3.52/0.99  
% 3.52/0.99  --superposition_flag                    true
% 3.52/0.99  --sup_passive_queue_type                priority_queues
% 3.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.99  --demod_completeness_check              fast
% 3.52/0.99  --demod_use_ground                      true
% 3.52/0.99  --sup_to_prop_solver                    passive
% 3.52/0.99  --sup_prop_simpl_new                    true
% 3.52/0.99  --sup_prop_simpl_given                  true
% 3.52/0.99  --sup_fun_splitting                     true
% 3.52/0.99  --sup_smt_interval                      50000
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Simplification Setup
% 3.52/0.99  
% 3.52/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.52/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.52/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.52/0.99  --sup_immed_triv                        [TrivRules]
% 3.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_bw_main                     []
% 3.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_input_bw                          []
% 3.52/0.99  
% 3.52/0.99  ------ Combination Options
% 3.52/0.99  
% 3.52/0.99  --comb_res_mult                         3
% 3.52/0.99  --comb_sup_mult                         2
% 3.52/0.99  --comb_inst_mult                        10
% 3.52/0.99  
% 3.52/0.99  ------ Debug Options
% 3.52/0.99  
% 3.52/0.99  --dbg_backtrace                         false
% 3.52/0.99  --dbg_dump_prop_clauses                 false
% 3.52/0.99  --dbg_dump_prop_clauses_file            -
% 3.52/0.99  --dbg_out_stat                          false
% 3.52/0.99  ------ Parsing...
% 3.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/0.99  ------ Proving...
% 3.52/0.99  ------ Problem Properties 
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  clauses                                 14
% 3.52/0.99  conjectures                             4
% 3.52/0.99  EPR                                     1
% 3.52/0.99  Horn                                    13
% 3.52/0.99  unary                                   9
% 3.52/0.99  binary                                  4
% 3.52/0.99  lits                                    20
% 3.52/0.99  lits eq                                 13
% 3.52/0.99  fd_pure                                 0
% 3.52/0.99  fd_pseudo                               0
% 3.52/0.99  fd_cond                                 0
% 3.52/0.99  fd_pseudo_cond                          1
% 3.52/0.99  AC symbols                              0
% 3.52/0.99  
% 3.52/0.99  ------ Schedule dynamic 5 is on 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ 
% 3.52/0.99  Current options:
% 3.52/0.99  ------ 
% 3.52/0.99  
% 3.52/0.99  ------ Input Options
% 3.52/0.99  
% 3.52/0.99  --out_options                           all
% 3.52/0.99  --tptp_safe_out                         true
% 3.52/0.99  --problem_path                          ""
% 3.52/0.99  --include_path                          ""
% 3.52/0.99  --clausifier                            res/vclausify_rel
% 3.52/0.99  --clausifier_options                    ""
% 3.52/0.99  --stdin                                 false
% 3.52/0.99  --stats_out                             all
% 3.52/0.99  
% 3.52/0.99  ------ General Options
% 3.52/0.99  
% 3.52/0.99  --fof                                   false
% 3.52/0.99  --time_out_real                         305.
% 3.52/0.99  --time_out_virtual                      -1.
% 3.52/0.99  --symbol_type_check                     false
% 3.52/0.99  --clausify_out                          false
% 3.52/0.99  --sig_cnt_out                           false
% 3.52/0.99  --trig_cnt_out                          false
% 3.52/0.99  --trig_cnt_out_tolerance                1.
% 3.52/0.99  --trig_cnt_out_sk_spl                   false
% 3.52/0.99  --abstr_cl_out                          false
% 3.52/0.99  
% 3.52/0.99  ------ Global Options
% 3.52/0.99  
% 3.52/0.99  --schedule                              default
% 3.52/0.99  --add_important_lit                     false
% 3.52/0.99  --prop_solver_per_cl                    1000
% 3.52/0.99  --min_unsat_core                        false
% 3.52/0.99  --soft_assumptions                      false
% 3.52/0.99  --soft_lemma_size                       3
% 3.52/0.99  --prop_impl_unit_size                   0
% 3.52/0.99  --prop_impl_unit                        []
% 3.52/0.99  --share_sel_clauses                     true
% 3.52/0.99  --reset_solvers                         false
% 3.52/0.99  --bc_imp_inh                            [conj_cone]
% 3.52/0.99  --conj_cone_tolerance                   3.
% 3.52/0.99  --extra_neg_conj                        none
% 3.52/0.99  --large_theory_mode                     true
% 3.52/0.99  --prolific_symb_bound                   200
% 3.52/0.99  --lt_threshold                          2000
% 3.52/0.99  --clause_weak_htbl                      true
% 3.52/0.99  --gc_record_bc_elim                     false
% 3.52/0.99  
% 3.52/0.99  ------ Preprocessing Options
% 3.52/0.99  
% 3.52/0.99  --preprocessing_flag                    true
% 3.52/0.99  --time_out_prep_mult                    0.1
% 3.52/0.99  --splitting_mode                        input
% 3.52/0.99  --splitting_grd                         true
% 3.52/0.99  --splitting_cvd                         false
% 3.52/0.99  --splitting_cvd_svl                     false
% 3.52/0.99  --splitting_nvd                         32
% 3.52/0.99  --sub_typing                            true
% 3.52/0.99  --prep_gs_sim                           true
% 3.52/0.99  --prep_unflatten                        true
% 3.52/0.99  --prep_res_sim                          true
% 3.52/0.99  --prep_upred                            true
% 3.52/0.99  --prep_sem_filter                       exhaustive
% 3.52/0.99  --prep_sem_filter_out                   false
% 3.52/0.99  --pred_elim                             true
% 3.52/0.99  --res_sim_input                         true
% 3.52/0.99  --eq_ax_congr_red                       true
% 3.52/0.99  --pure_diseq_elim                       true
% 3.52/0.99  --brand_transform                       false
% 3.52/0.99  --non_eq_to_eq                          false
% 3.52/0.99  --prep_def_merge                        true
% 3.52/0.99  --prep_def_merge_prop_impl              false
% 3.52/0.99  --prep_def_merge_mbd                    true
% 3.52/0.99  --prep_def_merge_tr_red                 false
% 3.52/0.99  --prep_def_merge_tr_cl                  false
% 3.52/0.99  --smt_preprocessing                     true
% 3.52/0.99  --smt_ac_axioms                         fast
% 3.52/0.99  --preprocessed_out                      false
% 3.52/0.99  --preprocessed_stats                    false
% 3.52/0.99  
% 3.52/0.99  ------ Abstraction refinement Options
% 3.52/0.99  
% 3.52/0.99  --abstr_ref                             []
% 3.52/0.99  --abstr_ref_prep                        false
% 3.52/0.99  --abstr_ref_until_sat                   false
% 3.52/0.99  --abstr_ref_sig_restrict                funpre
% 3.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/0.99  --abstr_ref_under                       []
% 3.52/0.99  
% 3.52/0.99  ------ SAT Options
% 3.52/0.99  
% 3.52/0.99  --sat_mode                              false
% 3.52/0.99  --sat_fm_restart_options                ""
% 3.52/0.99  --sat_gr_def                            false
% 3.52/0.99  --sat_epr_types                         true
% 3.52/0.99  --sat_non_cyclic_types                  false
% 3.52/0.99  --sat_finite_models                     false
% 3.52/0.99  --sat_fm_lemmas                         false
% 3.52/0.99  --sat_fm_prep                           false
% 3.52/0.99  --sat_fm_uc_incr                        true
% 3.52/0.99  --sat_out_model                         small
% 3.52/0.99  --sat_out_clauses                       false
% 3.52/0.99  
% 3.52/0.99  ------ QBF Options
% 3.52/0.99  
% 3.52/0.99  --qbf_mode                              false
% 3.52/0.99  --qbf_elim_univ                         false
% 3.52/0.99  --qbf_dom_inst                          none
% 3.52/0.99  --qbf_dom_pre_inst                      false
% 3.52/0.99  --qbf_sk_in                             false
% 3.52/0.99  --qbf_pred_elim                         true
% 3.52/0.99  --qbf_split                             512
% 3.52/0.99  
% 3.52/0.99  ------ BMC1 Options
% 3.52/0.99  
% 3.52/0.99  --bmc1_incremental                      false
% 3.52/0.99  --bmc1_axioms                           reachable_all
% 3.52/0.99  --bmc1_min_bound                        0
% 3.52/0.99  --bmc1_max_bound                        -1
% 3.52/0.99  --bmc1_max_bound_default                -1
% 3.52/0.99  --bmc1_symbol_reachability              true
% 3.52/0.99  --bmc1_property_lemmas                  false
% 3.52/0.99  --bmc1_k_induction                      false
% 3.52/0.99  --bmc1_non_equiv_states                 false
% 3.52/0.99  --bmc1_deadlock                         false
% 3.52/0.99  --bmc1_ucm                              false
% 3.52/0.99  --bmc1_add_unsat_core                   none
% 3.52/0.99  --bmc1_unsat_core_children              false
% 3.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/0.99  --bmc1_out_stat                         full
% 3.52/0.99  --bmc1_ground_init                      false
% 3.52/0.99  --bmc1_pre_inst_next_state              false
% 3.52/0.99  --bmc1_pre_inst_state                   false
% 3.52/0.99  --bmc1_pre_inst_reach_state             false
% 3.52/0.99  --bmc1_out_unsat_core                   false
% 3.52/0.99  --bmc1_aig_witness_out                  false
% 3.52/0.99  --bmc1_verbose                          false
% 3.52/0.99  --bmc1_dump_clauses_tptp                false
% 3.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.52/0.99  --bmc1_dump_file                        -
% 3.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.52/0.99  --bmc1_ucm_extend_mode                  1
% 3.52/0.99  --bmc1_ucm_init_mode                    2
% 3.52/0.99  --bmc1_ucm_cone_mode                    none
% 3.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.52/0.99  --bmc1_ucm_relax_model                  4
% 3.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/0.99  --bmc1_ucm_layered_model                none
% 3.52/0.99  --bmc1_ucm_max_lemma_size               10
% 3.52/0.99  
% 3.52/0.99  ------ AIG Options
% 3.52/0.99  
% 3.52/0.99  --aig_mode                              false
% 3.52/0.99  
% 3.52/0.99  ------ Instantiation Options
% 3.52/0.99  
% 3.52/0.99  --instantiation_flag                    true
% 3.52/0.99  --inst_sos_flag                         true
% 3.52/0.99  --inst_sos_phase                        true
% 3.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/0.99  --inst_lit_sel_side                     none
% 3.52/0.99  --inst_solver_per_active                1400
% 3.52/0.99  --inst_solver_calls_frac                1.
% 3.52/0.99  --inst_passive_queue_type               priority_queues
% 3.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/0.99  --inst_passive_queues_freq              [25;2]
% 3.52/0.99  --inst_dismatching                      true
% 3.52/0.99  --inst_eager_unprocessed_to_passive     true
% 3.52/0.99  --inst_prop_sim_given                   true
% 3.52/0.99  --inst_prop_sim_new                     false
% 3.52/0.99  --inst_subs_new                         false
% 3.52/0.99  --inst_eq_res_simp                      false
% 3.52/0.99  --inst_subs_given                       false
% 3.52/0.99  --inst_orphan_elimination               true
% 3.52/0.99  --inst_learning_loop_flag               true
% 3.52/0.99  --inst_learning_start                   3000
% 3.52/0.99  --inst_learning_factor                  2
% 3.52/0.99  --inst_start_prop_sim_after_learn       3
% 3.52/0.99  --inst_sel_renew                        solver
% 3.52/0.99  --inst_lit_activity_flag                true
% 3.52/0.99  --inst_restr_to_given                   false
% 3.52/0.99  --inst_activity_threshold               500
% 3.52/0.99  --inst_out_proof                        true
% 3.52/0.99  
% 3.52/0.99  ------ Resolution Options
% 3.52/0.99  
% 3.52/0.99  --resolution_flag                       false
% 3.52/0.99  --res_lit_sel                           adaptive
% 3.52/0.99  --res_lit_sel_side                      none
% 3.52/0.99  --res_ordering                          kbo
% 3.52/0.99  --res_to_prop_solver                    active
% 3.52/0.99  --res_prop_simpl_new                    false
% 3.52/0.99  --res_prop_simpl_given                  true
% 3.52/0.99  --res_passive_queue_type                priority_queues
% 3.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/0.99  --res_passive_queues_freq               [15;5]
% 3.52/0.99  --res_forward_subs                      full
% 3.52/0.99  --res_backward_subs                     full
% 3.52/0.99  --res_forward_subs_resolution           true
% 3.52/0.99  --res_backward_subs_resolution          true
% 3.52/0.99  --res_orphan_elimination                true
% 3.52/0.99  --res_time_limit                        2.
% 3.52/0.99  --res_out_proof                         true
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Options
% 3.52/0.99  
% 3.52/0.99  --superposition_flag                    true
% 3.52/0.99  --sup_passive_queue_type                priority_queues
% 3.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.52/0.99  --demod_completeness_check              fast
% 3.52/0.99  --demod_use_ground                      true
% 3.52/0.99  --sup_to_prop_solver                    passive
% 3.52/0.99  --sup_prop_simpl_new                    true
% 3.52/0.99  --sup_prop_simpl_given                  true
% 3.52/0.99  --sup_fun_splitting                     true
% 3.52/0.99  --sup_smt_interval                      50000
% 3.52/0.99  
% 3.52/0.99  ------ Superposition Simplification Setup
% 3.52/0.99  
% 3.52/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.52/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.52/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.52/0.99  --sup_immed_triv                        [TrivRules]
% 3.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_immed_bw_main                     []
% 3.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/0.99  --sup_input_bw                          []
% 3.52/0.99  
% 3.52/0.99  ------ Combination Options
% 3.52/0.99  
% 3.52/0.99  --comb_res_mult                         3
% 3.52/0.99  --comb_sup_mult                         2
% 3.52/0.99  --comb_inst_mult                        10
% 3.52/0.99  
% 3.52/0.99  ------ Debug Options
% 3.52/0.99  
% 3.52/0.99  --dbg_backtrace                         false
% 3.52/0.99  --dbg_dump_prop_clauses                 false
% 3.52/0.99  --dbg_dump_prop_clauses_file            -
% 3.52/0.99  --dbg_out_stat                          false
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  ------ Proving...
% 3.52/0.99  
% 3.52/0.99  
% 3.52/0.99  % SZS status Theorem for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/0.99  
% 3.52/0.99  fof(f17,conjecture,(
% 3.52/0.99    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f18,negated_conjecture,(
% 3.52/0.99    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.52/0.99    inference(negated_conjecture,[],[f17])).
% 3.52/0.99  
% 3.52/0.99  fof(f20,plain,(
% 3.52/0.99    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.52/0.99    inference(ennf_transformation,[],[f18])).
% 3.52/0.99  
% 3.52/0.99  fof(f23,plain,(
% 3.52/0.99    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 3.52/0.99    introduced(choice_axiom,[])).
% 3.52/0.99  
% 3.52/0.99  fof(f24,plain,(
% 3.52/0.99    (k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 3.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).
% 3.52/0.99  
% 3.52/0.99  fof(f43,plain,(
% 3.52/0.99    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 3.52/0.99    inference(cnf_transformation,[],[f24])).
% 3.52/0.99  
% 3.52/0.99  fof(f16,axiom,(
% 3.52/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f42,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.52/0.99    inference(cnf_transformation,[],[f16])).
% 3.52/0.99  
% 3.52/0.99  fof(f51,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.52/0.99    inference(definition_unfolding,[],[f42,f50])).
% 3.52/0.99  
% 3.52/0.99  fof(f9,axiom,(
% 3.52/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f33,plain,(
% 3.52/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f9])).
% 3.52/0.99  
% 3.52/0.99  fof(f10,axiom,(
% 3.52/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f34,plain,(
% 3.52/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f10])).
% 3.52/0.99  
% 3.52/0.99  fof(f11,axiom,(
% 3.52/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f35,plain,(
% 3.52/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f11])).
% 3.52/0.99  
% 3.52/0.99  fof(f14,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f38,plain,(
% 3.52/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.52/0.99    inference(cnf_transformation,[],[f14])).
% 3.52/0.99  
% 3.52/0.99  fof(f12,axiom,(
% 3.52/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/0.99  
% 3.52/0.99  fof(f36,plain,(
% 3.52/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f12])).
% 3.52/1.00  
% 3.52/1.00  fof(f13,axiom,(
% 3.52/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f37,plain,(
% 3.52/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f13])).
% 3.52/1.00  
% 3.52/1.00  fof(f47,plain,(
% 3.52/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f36,f37])).
% 3.52/1.00  
% 3.52/1.00  fof(f48,plain,(
% 3.52/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f38,f47])).
% 3.52/1.00  
% 3.52/1.00  fof(f49,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f35,f48])).
% 3.52/1.00  
% 3.52/1.00  fof(f50,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f34,f49])).
% 3.52/1.00  
% 3.52/1.00  fof(f53,plain,(
% 3.52/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f33,f50])).
% 3.52/1.00  
% 3.52/1.00  fof(f63,plain,(
% 3.52/1.00    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 3.52/1.00    inference(definition_unfolding,[],[f43,f51,f53])).
% 3.52/1.00  
% 3.52/1.00  fof(f5,axiom,(
% 3.52/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f29,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f5])).
% 3.52/1.00  
% 3.52/1.00  fof(f56,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f29,f51])).
% 3.52/1.00  
% 3.52/1.00  fof(f15,axiom,(
% 3.52/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f21,plain,(
% 3.52/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.52/1.00    inference(nnf_transformation,[],[f15])).
% 3.52/1.00  
% 3.52/1.00  fof(f22,plain,(
% 3.52/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.52/1.00    inference(flattening,[],[f21])).
% 3.52/1.00  
% 3.52/1.00  fof(f39,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f22])).
% 3.52/1.00  
% 3.52/1.00  fof(f59,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f39,f53,f53])).
% 3.52/1.00  
% 3.52/1.00  fof(f2,axiom,(
% 3.52/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f26,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f2])).
% 3.52/1.00  
% 3.52/1.00  fof(f8,axiom,(
% 3.52/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f32,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.52/1.00    inference(cnf_transformation,[],[f8])).
% 3.52/1.00  
% 3.52/1.00  fof(f52,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.52/1.00    inference(definition_unfolding,[],[f32,f51])).
% 3.52/1.00  
% 3.52/1.00  fof(f55,plain,(
% 3.52/1.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f26,f52])).
% 3.52/1.00  
% 3.52/1.00  fof(f7,axiom,(
% 3.52/1.00    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f31,plain,(
% 3.52/1.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f7])).
% 3.52/1.00  
% 3.52/1.00  fof(f6,axiom,(
% 3.52/1.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f30,plain,(
% 3.52/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f6])).
% 3.52/1.00  
% 3.52/1.00  fof(f4,axiom,(
% 3.52/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f28,plain,(
% 3.52/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.52/1.00    inference(cnf_transformation,[],[f4])).
% 3.52/1.00  
% 3.52/1.00  fof(f46,plain,(
% 3.52/1.00    k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1),
% 3.52/1.00    inference(cnf_transformation,[],[f24])).
% 3.52/1.00  
% 3.52/1.00  fof(f60,plain,(
% 3.52/1.00    k1_xboole_0 != sK2 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1),
% 3.52/1.00    inference(definition_unfolding,[],[f46,f53])).
% 3.52/1.00  
% 3.52/1.00  fof(f44,plain,(
% 3.52/1.00    k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1),
% 3.52/1.00    inference(cnf_transformation,[],[f24])).
% 3.52/1.00  
% 3.52/1.00  fof(f62,plain,(
% 3.52/1.00    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1),
% 3.52/1.00    inference(definition_unfolding,[],[f44,f53,f53])).
% 3.52/1.00  
% 3.52/1.00  fof(f45,plain,(
% 3.52/1.00    k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1),
% 3.52/1.00    inference(cnf_transformation,[],[f24])).
% 3.52/1.00  
% 3.52/1.00  fof(f61,plain,(
% 3.52/1.00    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 | k1_xboole_0 != sK1),
% 3.52/1.00    inference(definition_unfolding,[],[f45,f53])).
% 3.52/1.00  
% 3.52/1.00  fof(f3,axiom,(
% 3.52/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f27,plain,(
% 3.52/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f3])).
% 3.52/1.00  
% 3.52/1.00  fof(f1,axiom,(
% 3.52/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.52/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.00  
% 3.52/1.00  fof(f19,plain,(
% 3.52/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.52/1.00    inference(ennf_transformation,[],[f1])).
% 3.52/1.00  
% 3.52/1.00  fof(f25,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.52/1.00    inference(cnf_transformation,[],[f19])).
% 3.52/1.00  
% 3.52/1.00  fof(f54,plain,(
% 3.52/1.00    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.52/1.00    inference(definition_unfolding,[],[f25,f51])).
% 3.52/1.00  
% 3.52/1.00  cnf(c_13,negated_conjecture,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_4,plain,
% 3.52/1.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.52/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_279,plain,
% 3.52/1.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2219,plain,
% 3.52/1.00      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_13,c_279]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_9,plain,
% 3.52/1.00      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.52/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.52/1.00      | k1_xboole_0 = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_276,plain,
% 3.52/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 3.52/1.00      | k1_xboole_0 = X1
% 3.52/1.00      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2318,plain,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 3.52/1.00      | sK1 = k1_xboole_0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2219,c_276]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1,plain,
% 3.52/1.00      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_281,plain,
% 3.52/1.00      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_6,plain,
% 3.52/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_5,plain,
% 3.52/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.52/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_476,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_636,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_476,c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_796,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_636,c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_630,plain,
% 3.52/1.00      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_6,c_476]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.52/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_644,plain,
% 3.52/1.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_630,c_3]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_797,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_796,c_644]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_645,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_644,c_476]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1218,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_797,c_645]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1220,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_797,c_797]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1226,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
% 3.52/1.00      inference(splitting,
% 3.52/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.52/1.00                [c_1220]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1349,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,X1) = k5_xboole_0(X0,X1) ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_1218,c_1226]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2798,plain,
% 3.52/1.00      ( r1_tarski(k5_xboole_0(sP0_iProver_split(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
% 3.52/1.00      inference(light_normalisation,[status(thm)],[c_281,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2799,plain,
% 3.52/1.00      ( r1_tarski(sP0_iProver_split(sP0_iProver_split(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_2798,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_478,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_878,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_478,c_645]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_886,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_878,c_3]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_898,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_886,c_5]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1526,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,X0),X2)) = sP0_iProver_split(X1,X2) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_898,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1527,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X1,X0),X2)) = sP0_iProver_split(X1,X2) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_1526,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_892,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_5,c_886]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1407,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,X0))) = sP0_iProver_split(X1,X2) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_892,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1408,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,X0))) = sP0_iProver_split(X1,X2) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_1407,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1536,plain,
% 3.52/1.00      ( sP0_iProver_split(sP0_iProver_split(X0,X1),X2) = sP0_iProver_split(X0,sP0_iProver_split(X2,X1)) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_1527,c_1408]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2800,plain,
% 3.52/1.00      ( r1_tarski(sP0_iProver_split(X0,sP0_iProver_split(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1)),X0) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_2799,c_1536]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2814,plain,
% 3.52/1.00      ( r1_tarski(sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)),sK1) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_13,c_2800]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3180,plain,
% 3.52/1.00      ( sK1 = k1_xboole_0
% 3.52/1.00      | r1_tarski(sP0_iProver_split(sK1,sP0_iProver_split(sK1,sK2)),sK1) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2318,c_2814]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1215,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_886,c_797]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1357,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X2,X1) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_1215,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1358,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,X2))) = sP0_iProver_split(X2,X1) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_1357,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_895,plain,
% 3.52/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_645,c_886]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1217,plain,
% 3.52/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X0)))) = X2 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_797,c_895]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1354,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,k5_xboole_0(X1,X0)))) = X2 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_1217,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1355,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,k5_xboole_0(X1,X0)))) = X2 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_1354,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1356,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,sP0_iProver_split(X1,X0)))) = X2 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_1355,c_1349]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_1359,plain,
% 3.52/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X0,X1)) = X1 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_1358,c_1356]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3182,plain,
% 3.52/1.00      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK1) = iProver_top ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_3180,c_1359]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_10,negated_conjecture,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
% 3.52/1.00      | k1_xboole_0 != sK2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2326,plain,
% 3.52/1.00      ( sK1 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2318,c_10]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2322,plain,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
% 3.52/1.00      | sK1 = k1_xboole_0
% 3.52/1.00      | k1_xboole_0 = X0
% 3.52/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2318,c_276]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3181,plain,
% 3.52/1.00      ( sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 3.52/1.00      | sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
% 3.52/1.00      | sK1 = k1_xboole_0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2814,c_2322]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3421,plain,
% 3.52/1.00      ( sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
% 3.52/1.00      | sK1 = k1_xboole_0
% 3.52/1.00      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_3181,c_2814]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_12,negated_conjecture,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
% 3.52/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
% 3.52/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2324,plain,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
% 3.52/1.00      | sK1 = k1_xboole_0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2318,c_12]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_11,negated_conjecture,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
% 3.52/1.00      | k1_xboole_0 != sK1 ),
% 3.52/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_296,plain,
% 3.52/1.00      ( ~ r1_tarski(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.52/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK1
% 3.52/1.00      | k1_xboole_0 = sK1 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_298,plain,
% 3.52/1.00      ( ~ r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.52/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 3.52/1.00      | k1_xboole_0 = sK1 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_296]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_159,plain,( X0 = X0 ),theory(equality) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_375,plain,
% 3.52/1.00      ( sK1 = sK1 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_159]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_163,plain,
% 3.52/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.52/1.00      theory(equality) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_422,plain,
% 3.52/1.00      ( r1_tarski(X0,X1)
% 3.52/1.00      | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
% 3.52/1.00      | X0 != X2
% 3.52/1.00      | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_163]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_650,plain,
% 3.52/1.00      ( r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.52/1.00      | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 3.52/1.00      | X0 != sK1
% 3.52/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_422]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_772,plain,
% 3.52/1.00      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.52/1.00      | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 3.52/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.52/1.00      | sK1 != sK1 ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_650]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_514,plain,
% 3.52/1.00      ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_932,plain,
% 3.52/1.00      ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
% 3.52/1.00      inference(instantiation,[status(thm)],[c_514]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2412,plain,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_2324,c_13,c_12,c_11,c_298,c_375,c_772,c_932]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3399,plain,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sP0_iProver_split(sK1,sP0_iProver_split(sK1,sK2))
% 3.52/1.00      | sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
% 3.52/1.00      | sK1 = k1_xboole_0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2318,c_3181]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3429,plain,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2
% 3.52/1.00      | sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
% 3.52/1.00      | sK1 = k1_xboole_0 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_3399,c_1359]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3536,plain,
% 3.52/1.00      ( sK1 = k1_xboole_0
% 3.52/1.00      | sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_3421,c_13,c_12,c_11,c_298,c_375,c_772,c_932,c_3429]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3537,plain,
% 3.52/1.00      ( sP0_iProver_split(sK1,sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) = k1_xboole_0
% 3.52/1.00      | sK1 = k1_xboole_0 ),
% 3.52/1.00      inference(renaming,[status(thm)],[c_3536]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3540,plain,
% 3.52/1.00      ( sP0_iProver_split(sK1,sP0_iProver_split(sK1,sK2)) = k1_xboole_0
% 3.52/1.00      | sK1 = k1_xboole_0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_2318,c_3537]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3576,plain,
% 3.52/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_3540,c_1359]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3671,plain,
% 3.52/1.00      ( sK1 = k1_xboole_0 ),
% 3.52/1.00      inference(global_propositional_subsumption,
% 3.52/1.00                [status(thm)],
% 3.52/1.00                [c_3182,c_2326,c_3576]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3683,plain,
% 3.52/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_3671,c_13]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_2,plain,
% 3.52/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.52/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_280,plain,
% 3.52/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_0,plain,
% 3.52/1.00      ( ~ r1_tarski(X0,X1)
% 3.52/1.00      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 3.52/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_282,plain,
% 3.52/1.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 3.52/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.52/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3186,plain,
% 3.52/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.52/1.00      inference(superposition,[status(thm)],[c_280,c_282]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(c_3685,plain,
% 3.52/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2 ),
% 3.52/1.00      inference(demodulation,[status(thm)],[c_3683,c_3186]) ).
% 3.52/1.00  
% 3.52/1.00  cnf(contradiction,plain,
% 3.52/1.00      ( $false ),
% 3.52/1.00      inference(minisat,[status(thm)],[c_3685,c_2412]) ).
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/1.00  
% 3.52/1.00  ------                               Statistics
% 3.52/1.00  
% 3.52/1.00  ------ General
% 3.52/1.00  
% 3.52/1.00  abstr_ref_over_cycles:                  0
% 3.52/1.00  abstr_ref_under_cycles:                 0
% 3.52/1.00  gc_basic_clause_elim:                   0
% 3.52/1.00  forced_gc_time:                         0
% 3.52/1.00  parsing_time:                           0.01
% 3.52/1.00  unif_index_cands_time:                  0.
% 3.52/1.00  unif_index_add_time:                    0.
% 3.52/1.00  orderings_time:                         0.
% 3.52/1.00  out_proof_time:                         0.029
% 3.52/1.00  total_time:                             0.208
% 3.52/1.00  num_of_symbols:                         40
% 3.52/1.00  num_of_terms:                           5490
% 3.52/1.00  
% 3.52/1.00  ------ Preprocessing
% 3.52/1.00  
% 3.52/1.00  num_of_splits:                          0
% 3.52/1.00  num_of_split_atoms:                     1
% 3.52/1.00  num_of_reused_defs:                     0
% 3.52/1.00  num_eq_ax_congr_red:                    0
% 3.52/1.00  num_of_sem_filtered_clauses:            1
% 3.52/1.00  num_of_subtypes:                        0
% 3.52/1.00  monotx_restored_types:                  0
% 3.52/1.00  sat_num_of_epr_types:                   0
% 3.52/1.00  sat_num_of_non_cyclic_types:            0
% 3.52/1.00  sat_guarded_non_collapsed_types:        0
% 3.52/1.00  num_pure_diseq_elim:                    0
% 3.52/1.00  simp_replaced_by:                       0
% 3.52/1.00  res_preprocessed:                       55
% 3.52/1.00  prep_upred:                             0
% 3.52/1.00  prep_unflattend:                        17
% 3.52/1.00  smt_new_axioms:                         0
% 3.52/1.00  pred_elim_cands:                        1
% 3.52/1.00  pred_elim:                              0
% 3.52/1.00  pred_elim_cl:                           0
% 3.52/1.00  pred_elim_cycles:                       1
% 3.52/1.00  merged_defs:                            0
% 3.52/1.00  merged_defs_ncl:                        0
% 3.52/1.00  bin_hyper_res:                          0
% 3.52/1.00  prep_cycles:                            3
% 3.52/1.00  pred_elim_time:                         0.002
% 3.52/1.00  splitting_time:                         0.
% 3.52/1.00  sem_filter_time:                        0.
% 3.52/1.00  monotx_time:                            0.
% 3.52/1.00  subtype_inf_time:                       0.
% 3.52/1.00  
% 3.52/1.00  ------ Problem properties
% 3.52/1.00  
% 3.52/1.00  clauses:                                14
% 3.52/1.00  conjectures:                            4
% 3.52/1.00  epr:                                    1
% 3.52/1.00  horn:                                   13
% 3.52/1.00  ground:                                 4
% 3.52/1.00  unary:                                  9
% 3.52/1.00  binary:                                 4
% 3.52/1.00  lits:                                   20
% 3.52/1.00  lits_eq:                                13
% 3.52/1.00  fd_pure:                                0
% 3.52/1.00  fd_pseudo:                              0
% 3.52/1.00  fd_cond:                                0
% 3.52/1.00  fd_pseudo_cond:                         1
% 3.52/1.00  ac_symbols:                             2
% 3.52/1.00  
% 3.52/1.00  ------ Propositional Solver
% 3.52/1.00  
% 3.52/1.00  prop_solver_calls:                      25
% 3.52/1.00  prop_fast_solver_calls:                 309
% 3.52/1.00  smt_solver_calls:                       0
% 3.52/1.00  smt_fast_solver_calls:                  0
% 3.52/1.00  prop_num_of_clauses:                    1621
% 3.52/1.00  prop_preprocess_simplified:             4122
% 3.52/1.00  prop_fo_subsumed:                       3
% 3.52/1.00  prop_solver_time:                       0.
% 3.52/1.00  smt_solver_time:                        0.
% 3.52/1.00  smt_fast_solver_time:                   0.
% 3.52/1.00  prop_fast_solver_time:                  0.
% 3.52/1.00  prop_unsat_core_time:                   0.
% 3.52/1.00  
% 3.52/1.00  ------ QBF
% 3.52/1.00  
% 3.52/1.00  qbf_q_res:                              0
% 3.52/1.00  qbf_num_tautologies:                    0
% 3.52/1.00  qbf_prep_cycles:                        0
% 3.52/1.00  
% 3.52/1.00  ------ BMC1
% 3.52/1.00  
% 3.52/1.00  bmc1_current_bound:                     -1
% 3.52/1.00  bmc1_last_solved_bound:                 -1
% 3.52/1.00  bmc1_unsat_core_size:                   -1
% 3.52/1.00  bmc1_unsat_core_parents_size:           -1
% 3.52/1.00  bmc1_merge_next_fun:                    0
% 3.52/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.52/1.00  
% 3.52/1.00  ------ Instantiation
% 3.52/1.00  
% 3.52/1.00  inst_num_of_clauses:                    516
% 3.52/1.00  inst_num_in_passive:                    217
% 3.52/1.00  inst_num_in_active:                     236
% 3.52/1.00  inst_num_in_unprocessed:                63
% 3.52/1.00  inst_num_of_loops:                      270
% 3.52/1.00  inst_num_of_learning_restarts:          0
% 3.52/1.00  inst_num_moves_active_passive:          30
% 3.52/1.00  inst_lit_activity:                      0
% 3.52/1.00  inst_lit_activity_moves:                0
% 3.52/1.00  inst_num_tautologies:                   0
% 3.52/1.00  inst_num_prop_implied:                  0
% 3.52/1.00  inst_num_existing_simplified:           0
% 3.52/1.00  inst_num_eq_res_simplified:             0
% 3.52/1.00  inst_num_child_elim:                    0
% 3.52/1.00  inst_num_of_dismatching_blockings:      239
% 3.52/1.00  inst_num_of_non_proper_insts:           552
% 3.52/1.00  inst_num_of_duplicates:                 0
% 3.52/1.00  inst_inst_num_from_inst_to_res:         0
% 3.52/1.00  inst_dismatching_checking_time:         0.
% 3.52/1.00  
% 3.52/1.00  ------ Resolution
% 3.52/1.00  
% 3.52/1.00  res_num_of_clauses:                     0
% 3.52/1.00  res_num_in_passive:                     0
% 3.52/1.00  res_num_in_active:                      0
% 3.52/1.00  res_num_of_loops:                       58
% 3.52/1.00  res_forward_subset_subsumed:            75
% 3.52/1.00  res_backward_subset_subsumed:           0
% 3.52/1.00  res_forward_subsumed:                   1
% 3.52/1.00  res_backward_subsumed:                  0
% 3.52/1.00  res_forward_subsumption_resolution:     0
% 3.52/1.00  res_backward_subsumption_resolution:    0
% 3.52/1.00  res_clause_to_clause_subsumption:       989
% 3.52/1.00  res_orphan_elimination:                 0
% 3.52/1.00  res_tautology_del:                      45
% 3.52/1.00  res_num_eq_res_simplified:              0
% 3.52/1.00  res_num_sel_changes:                    0
% 3.52/1.00  res_moves_from_active_to_pass:          0
% 3.52/1.00  
% 3.52/1.00  ------ Superposition
% 3.52/1.00  
% 3.52/1.00  sup_time_total:                         0.
% 3.52/1.00  sup_time_generating:                    0.
% 3.52/1.00  sup_time_sim_full:                      0.
% 3.52/1.00  sup_time_sim_immed:                     0.
% 3.52/1.00  
% 3.52/1.00  sup_num_of_clauses:                     131
% 3.52/1.00  sup_num_in_active:                      22
% 3.52/1.00  sup_num_in_passive:                     109
% 3.52/1.00  sup_num_of_loops:                       52
% 3.52/1.00  sup_fw_superposition:                   278
% 3.52/1.00  sup_bw_superposition:                   251
% 3.52/1.00  sup_immediate_simplified:               134
% 3.52/1.00  sup_given_eliminated:                   4
% 3.52/1.00  comparisons_done:                       0
% 3.52/1.00  comparisons_avoided:                    6
% 3.52/1.00  
% 3.52/1.00  ------ Simplifications
% 3.52/1.00  
% 3.52/1.00  
% 3.52/1.00  sim_fw_subset_subsumed:                 0
% 3.52/1.00  sim_bw_subset_subsumed:                 7
% 3.52/1.00  sim_fw_subsumed:                        17
% 3.52/1.00  sim_bw_subsumed:                        3
% 3.52/1.00  sim_fw_subsumption_res:                 0
% 3.52/1.00  sim_bw_subsumption_res:                 0
% 3.52/1.00  sim_tautology_del:                      1
% 3.52/1.00  sim_eq_tautology_del:                   36
% 3.52/1.00  sim_eq_res_simp:                        0
% 3.52/1.00  sim_fw_demodulated:                     143
% 3.52/1.00  sim_bw_demodulated:                     37
% 3.52/1.00  sim_light_normalised:                   41
% 3.52/1.00  sim_joinable_taut:                      6
% 3.52/1.00  sim_joinable_simp:                      0
% 3.52/1.00  sim_ac_normalised:                      0
% 3.52/1.00  sim_smt_subsumption:                    0
% 3.52/1.00  
%------------------------------------------------------------------------------
