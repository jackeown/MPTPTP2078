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

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  150 (10227 expanded)
%              Number of clauses        :   85 (4159 expanded)
%              Number of leaves         :   22 (2699 expanded)
%              Depth                    :   27
%              Number of atoms          :  257 (11500 expanded)
%              Number of equality atoms :  220 (11291 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f25,plain,
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

fof(f26,plain,
    ( ( k1_xboole_0 != sK2
      | k1_tarski(sK0) != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_xboole_0 != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_tarski(sK0) != sK1 )
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).

fof(f47,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f69,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f47,f56,f59])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f32,f56])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f43,f59,f59])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f27,f57])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(definition_unfolding,[],[f30,f58])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,
    ( k1_xboole_0 != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,
    ( k1_xboole_0 != sK2
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f48,plain,
    ( k1_tarski(sK0) != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f48,f59,f59])).

fof(f49,plain,
    ( k1_tarski(sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f56])).

cnf(c_13,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_279,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2228,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_279])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_276,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2331,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2228,c_276])).

cnf(c_2,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_280,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_476,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_636,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_476,c_5])).

cnf(c_801,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(light_normalisation,[status(thm)],[c_636,c_5])).

cnf(c_630,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_476])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_644,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_630,c_3])).

cnf(c_802,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(demodulation,[status(thm)],[c_801,c_644])).

cnf(c_645,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_644,c_476])).

cnf(c_1223,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_802,c_645])).

cnf(c_1225,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
    inference(superposition,[status(thm)],[c_802,c_802])).

cnf(c_1231,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1225])).

cnf(c_1354,plain,
    ( sP0_iProver_split(X0,X1) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1223,c_1231])).

cnf(c_2822,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_280,c_1354])).

cnf(c_2823,plain,
    ( r1_tarski(sP0_iProver_split(X0,k5_xboole_0(sP0_iProver_split(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2822,c_1354])).

cnf(c_1224,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_802,c_5])).

cnf(c_1353,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_1224,c_1231])).

cnf(c_1356,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(X0,X1),X2)) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_1354,c_1353])).

cnf(c_1357,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X0,X1),X2)) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_1356,c_1354])).

cnf(c_2824,plain,
    ( r1_tarski(sP0_iProver_split(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2823,c_1354,c_1357])).

cnf(c_2829,plain,
    ( r1_tarski(sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_2824])).

cnf(c_2335,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2331,c_276])).

cnf(c_3014,plain,
    ( sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2829,c_2335])).

cnf(c_3427,plain,
    ( sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_2829])).

cnf(c_10,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2339,plain,
    ( sK1 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2331,c_10])).

cnf(c_478,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_883,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_478,c_645])).

cnf(c_891,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_883,c_3])).

cnf(c_906,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_891,c_891])).

cnf(c_1218,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X2))) = X1 ),
    inference(superposition,[status(thm)],[c_906,c_802])).

cnf(c_1367,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,X2),k5_xboole_0(X0,X2))) = X1 ),
    inference(demodulation,[status(thm)],[c_1218,c_1354])).

cnf(c_1220,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_891,c_802])).

cnf(c_1362,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X2,X1) ),
    inference(demodulation,[status(thm)],[c_1220,c_1354])).

cnf(c_1363,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,X2))) = sP0_iProver_split(X2,X1) ),
    inference(demodulation,[status(thm)],[c_1362,c_1354])).

cnf(c_1368,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1367,c_1354,c_1363])).

cnf(c_3417,plain,
    ( sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK2
    | sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3014,c_1368])).

cnf(c_2069,plain,
    ( sP0_iProver_split(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1354,c_6])).

cnf(c_3429,plain,
    ( sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3417,c_2069])).

cnf(c_3531,plain,
    ( sK1 = k1_xboole_0
    | sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3427,c_2339,c_3429])).

cnf(c_3532,plain,
    ( sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3531])).

cnf(c_3533,plain,
    ( sP0_iProver_split(sK2,sK1) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2331,c_3532])).

cnf(c_12,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2337,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2331,c_12])).

cnf(c_11,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f67])).

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

cnf(c_777,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_514,plain,
    ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_937,plain,
    ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_2435,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2337,c_13,c_12,c_11,c_298,c_375,c_777,c_937])).

cnf(c_3542,plain,
    ( sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3532,c_1368])).

cnf(c_1213,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) = X1 ),
    inference(superposition,[status(thm)],[c_6,c_802])).

cnf(c_1372,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X0,k1_xboole_0))) = X1 ),
    inference(demodulation,[status(thm)],[c_1213,c_1354])).

cnf(c_1373,plain,
    ( sP0_iProver_split(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1372,c_1354,c_1363])).

cnf(c_897,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_5,c_891])).

cnf(c_1412,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,X0))) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_897,c_1354])).

cnf(c_1413,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,X0))) = sP0_iProver_split(X1,X2) ),
    inference(demodulation,[status(thm)],[c_1412,c_1354])).

cnf(c_1762,plain,
    ( sP0_iProver_split(X0,sP0_iProver_split(X1,X0)) = sP0_iProver_split(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1373,c_1413])).

cnf(c_1766,plain,
    ( sP0_iProver_split(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1762,c_1368])).

cnf(c_3556,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3542,c_1766])).

cnf(c_3567,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3533,c_13,c_12,c_11,c_298,c_375,c_777,c_937,c_3556])).

cnf(c_3576,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_3567,c_13])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_281,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_282,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3017,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_281,c_282])).

cnf(c_3578,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_3576,c_3017])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3578,c_2435])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.93/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/1.00  
% 3.93/1.00  ------  iProver source info
% 3.93/1.00  
% 3.93/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.93/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/1.00  git: non_committed_changes: false
% 3.93/1.00  git: last_make_outside_of_git: false
% 3.93/1.00  
% 3.93/1.00  ------ 
% 3.93/1.00  
% 3.93/1.00  ------ Input Options
% 3.93/1.00  
% 3.93/1.00  --out_options                           all
% 3.93/1.00  --tptp_safe_out                         true
% 3.93/1.00  --problem_path                          ""
% 3.93/1.00  --include_path                          ""
% 3.93/1.00  --clausifier                            res/vclausify_rel
% 3.93/1.00  --clausifier_options                    ""
% 3.93/1.00  --stdin                                 false
% 3.93/1.00  --stats_out                             all
% 3.93/1.00  
% 3.93/1.00  ------ General Options
% 3.93/1.00  
% 3.93/1.00  --fof                                   false
% 3.93/1.00  --time_out_real                         305.
% 3.93/1.00  --time_out_virtual                      -1.
% 3.93/1.00  --symbol_type_check                     false
% 3.93/1.00  --clausify_out                          false
% 3.93/1.00  --sig_cnt_out                           false
% 3.93/1.00  --trig_cnt_out                          false
% 3.93/1.00  --trig_cnt_out_tolerance                1.
% 3.93/1.00  --trig_cnt_out_sk_spl                   false
% 3.93/1.00  --abstr_cl_out                          false
% 3.93/1.00  
% 3.93/1.00  ------ Global Options
% 3.93/1.00  
% 3.93/1.00  --schedule                              default
% 3.93/1.00  --add_important_lit                     false
% 3.93/1.00  --prop_solver_per_cl                    1000
% 3.93/1.00  --min_unsat_core                        false
% 3.93/1.00  --soft_assumptions                      false
% 3.93/1.00  --soft_lemma_size                       3
% 3.93/1.00  --prop_impl_unit_size                   0
% 3.93/1.00  --prop_impl_unit                        []
% 3.93/1.00  --share_sel_clauses                     true
% 3.93/1.00  --reset_solvers                         false
% 3.93/1.00  --bc_imp_inh                            [conj_cone]
% 3.93/1.00  --conj_cone_tolerance                   3.
% 3.93/1.00  --extra_neg_conj                        none
% 3.93/1.00  --large_theory_mode                     true
% 3.93/1.00  --prolific_symb_bound                   200
% 3.93/1.00  --lt_threshold                          2000
% 3.93/1.00  --clause_weak_htbl                      true
% 3.93/1.00  --gc_record_bc_elim                     false
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing Options
% 3.93/1.00  
% 3.93/1.00  --preprocessing_flag                    true
% 3.93/1.00  --time_out_prep_mult                    0.1
% 3.93/1.00  --splitting_mode                        input
% 3.93/1.00  --splitting_grd                         true
% 3.93/1.00  --splitting_cvd                         false
% 3.93/1.00  --splitting_cvd_svl                     false
% 3.93/1.00  --splitting_nvd                         32
% 3.93/1.00  --sub_typing                            true
% 3.93/1.00  --prep_gs_sim                           true
% 3.93/1.00  --prep_unflatten                        true
% 3.93/1.00  --prep_res_sim                          true
% 3.93/1.00  --prep_upred                            true
% 3.93/1.00  --prep_sem_filter                       exhaustive
% 3.93/1.00  --prep_sem_filter_out                   false
% 3.93/1.00  --pred_elim                             true
% 3.93/1.00  --res_sim_input                         true
% 3.93/1.00  --eq_ax_congr_red                       true
% 3.93/1.00  --pure_diseq_elim                       true
% 3.93/1.00  --brand_transform                       false
% 3.93/1.00  --non_eq_to_eq                          false
% 3.93/1.00  --prep_def_merge                        true
% 3.93/1.00  --prep_def_merge_prop_impl              false
% 3.93/1.00  --prep_def_merge_mbd                    true
% 3.93/1.00  --prep_def_merge_tr_red                 false
% 3.93/1.00  --prep_def_merge_tr_cl                  false
% 3.93/1.00  --smt_preprocessing                     true
% 3.93/1.00  --smt_ac_axioms                         fast
% 3.93/1.00  --preprocessed_out                      false
% 3.93/1.00  --preprocessed_stats                    false
% 3.93/1.00  
% 3.93/1.00  ------ Abstraction refinement Options
% 3.93/1.00  
% 3.93/1.00  --abstr_ref                             []
% 3.93/1.00  --abstr_ref_prep                        false
% 3.93/1.00  --abstr_ref_until_sat                   false
% 3.93/1.00  --abstr_ref_sig_restrict                funpre
% 3.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/1.00  --abstr_ref_under                       []
% 3.93/1.00  
% 3.93/1.00  ------ SAT Options
% 3.93/1.00  
% 3.93/1.00  --sat_mode                              false
% 3.93/1.00  --sat_fm_restart_options                ""
% 3.93/1.00  --sat_gr_def                            false
% 3.93/1.00  --sat_epr_types                         true
% 3.93/1.00  --sat_non_cyclic_types                  false
% 3.93/1.00  --sat_finite_models                     false
% 3.93/1.00  --sat_fm_lemmas                         false
% 3.93/1.00  --sat_fm_prep                           false
% 3.93/1.00  --sat_fm_uc_incr                        true
% 3.93/1.00  --sat_out_model                         small
% 3.93/1.00  --sat_out_clauses                       false
% 3.93/1.00  
% 3.93/1.00  ------ QBF Options
% 3.93/1.00  
% 3.93/1.00  --qbf_mode                              false
% 3.93/1.00  --qbf_elim_univ                         false
% 3.93/1.00  --qbf_dom_inst                          none
% 3.93/1.00  --qbf_dom_pre_inst                      false
% 3.93/1.00  --qbf_sk_in                             false
% 3.93/1.00  --qbf_pred_elim                         true
% 3.93/1.00  --qbf_split                             512
% 3.93/1.00  
% 3.93/1.00  ------ BMC1 Options
% 3.93/1.00  
% 3.93/1.00  --bmc1_incremental                      false
% 3.93/1.00  --bmc1_axioms                           reachable_all
% 3.93/1.00  --bmc1_min_bound                        0
% 3.93/1.00  --bmc1_max_bound                        -1
% 3.93/1.00  --bmc1_max_bound_default                -1
% 3.93/1.00  --bmc1_symbol_reachability              true
% 3.93/1.00  --bmc1_property_lemmas                  false
% 3.93/1.00  --bmc1_k_induction                      false
% 3.93/1.00  --bmc1_non_equiv_states                 false
% 3.93/1.00  --bmc1_deadlock                         false
% 3.93/1.00  --bmc1_ucm                              false
% 3.93/1.00  --bmc1_add_unsat_core                   none
% 3.93/1.00  --bmc1_unsat_core_children              false
% 3.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/1.00  --bmc1_out_stat                         full
% 3.93/1.00  --bmc1_ground_init                      false
% 3.93/1.00  --bmc1_pre_inst_next_state              false
% 3.93/1.00  --bmc1_pre_inst_state                   false
% 3.93/1.00  --bmc1_pre_inst_reach_state             false
% 3.93/1.00  --bmc1_out_unsat_core                   false
% 3.93/1.00  --bmc1_aig_witness_out                  false
% 3.93/1.00  --bmc1_verbose                          false
% 3.93/1.00  --bmc1_dump_clauses_tptp                false
% 3.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.93/1.00  --bmc1_dump_file                        -
% 3.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.93/1.00  --bmc1_ucm_extend_mode                  1
% 3.93/1.00  --bmc1_ucm_init_mode                    2
% 3.93/1.00  --bmc1_ucm_cone_mode                    none
% 3.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.93/1.00  --bmc1_ucm_relax_model                  4
% 3.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/1.00  --bmc1_ucm_layered_model                none
% 3.93/1.00  --bmc1_ucm_max_lemma_size               10
% 3.93/1.00  
% 3.93/1.00  ------ AIG Options
% 3.93/1.00  
% 3.93/1.00  --aig_mode                              false
% 3.93/1.00  
% 3.93/1.00  ------ Instantiation Options
% 3.93/1.00  
% 3.93/1.00  --instantiation_flag                    true
% 3.93/1.00  --inst_sos_flag                         true
% 3.93/1.00  --inst_sos_phase                        true
% 3.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel_side                     num_symb
% 3.93/1.00  --inst_solver_per_active                1400
% 3.93/1.00  --inst_solver_calls_frac                1.
% 3.93/1.00  --inst_passive_queue_type               priority_queues
% 3.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/1.00  --inst_passive_queues_freq              [25;2]
% 3.93/1.00  --inst_dismatching                      true
% 3.93/1.00  --inst_eager_unprocessed_to_passive     true
% 3.93/1.00  --inst_prop_sim_given                   true
% 3.93/1.00  --inst_prop_sim_new                     false
% 3.93/1.00  --inst_subs_new                         false
% 3.93/1.00  --inst_eq_res_simp                      false
% 3.93/1.00  --inst_subs_given                       false
% 3.93/1.00  --inst_orphan_elimination               true
% 3.93/1.00  --inst_learning_loop_flag               true
% 3.93/1.00  --inst_learning_start                   3000
% 3.93/1.00  --inst_learning_factor                  2
% 3.93/1.00  --inst_start_prop_sim_after_learn       3
% 3.93/1.00  --inst_sel_renew                        solver
% 3.93/1.00  --inst_lit_activity_flag                true
% 3.93/1.00  --inst_restr_to_given                   false
% 3.93/1.00  --inst_activity_threshold               500
% 3.93/1.00  --inst_out_proof                        true
% 3.93/1.00  
% 3.93/1.00  ------ Resolution Options
% 3.93/1.00  
% 3.93/1.00  --resolution_flag                       true
% 3.93/1.00  --res_lit_sel                           adaptive
% 3.93/1.00  --res_lit_sel_side                      none
% 3.93/1.00  --res_ordering                          kbo
% 3.93/1.00  --res_to_prop_solver                    active
% 3.93/1.00  --res_prop_simpl_new                    false
% 3.93/1.00  --res_prop_simpl_given                  true
% 3.93/1.00  --res_passive_queue_type                priority_queues
% 3.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/1.00  --res_passive_queues_freq               [15;5]
% 3.93/1.00  --res_forward_subs                      full
% 3.93/1.00  --res_backward_subs                     full
% 3.93/1.00  --res_forward_subs_resolution           true
% 3.93/1.00  --res_backward_subs_resolution          true
% 3.93/1.00  --res_orphan_elimination                true
% 3.93/1.00  --res_time_limit                        2.
% 3.93/1.00  --res_out_proof                         true
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Options
% 3.93/1.00  
% 3.93/1.00  --superposition_flag                    true
% 3.93/1.00  --sup_passive_queue_type                priority_queues
% 3.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.93/1.00  --demod_completeness_check              fast
% 3.93/1.00  --demod_use_ground                      true
% 3.93/1.00  --sup_to_prop_solver                    passive
% 3.93/1.00  --sup_prop_simpl_new                    true
% 3.93/1.00  --sup_prop_simpl_given                  true
% 3.93/1.00  --sup_fun_splitting                     true
% 3.93/1.00  --sup_smt_interval                      50000
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Simplification Setup
% 3.93/1.00  
% 3.93/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/1.00  --sup_immed_triv                        [TrivRules]
% 3.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_immed_bw_main                     []
% 3.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_input_bw                          []
% 3.93/1.00  
% 3.93/1.00  ------ Combination Options
% 3.93/1.00  
% 3.93/1.00  --comb_res_mult                         3
% 3.93/1.00  --comb_sup_mult                         2
% 3.93/1.00  --comb_inst_mult                        10
% 3.93/1.00  
% 3.93/1.00  ------ Debug Options
% 3.93/1.00  
% 3.93/1.00  --dbg_backtrace                         false
% 3.93/1.00  --dbg_dump_prop_clauses                 false
% 3.93/1.00  --dbg_dump_prop_clauses_file            -
% 3.93/1.00  --dbg_out_stat                          false
% 3.93/1.00  ------ Parsing...
% 3.93/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/1.00  ------ Proving...
% 3.93/1.00  ------ Problem Properties 
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  clauses                                 14
% 3.93/1.00  conjectures                             4
% 3.93/1.00  EPR                                     1
% 3.93/1.00  Horn                                    13
% 3.93/1.00  unary                                   9
% 3.93/1.00  binary                                  4
% 3.93/1.00  lits                                    20
% 3.93/1.00  lits eq                                 13
% 3.93/1.00  fd_pure                                 0
% 3.93/1.00  fd_pseudo                               0
% 3.93/1.00  fd_cond                                 0
% 3.93/1.00  fd_pseudo_cond                          1
% 3.93/1.00  AC symbols                              0
% 3.93/1.00  
% 3.93/1.00  ------ Schedule dynamic 5 is on 
% 3.93/1.00  
% 3.93/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ 
% 3.93/1.00  Current options:
% 3.93/1.00  ------ 
% 3.93/1.00  
% 3.93/1.00  ------ Input Options
% 3.93/1.00  
% 3.93/1.00  --out_options                           all
% 3.93/1.00  --tptp_safe_out                         true
% 3.93/1.00  --problem_path                          ""
% 3.93/1.00  --include_path                          ""
% 3.93/1.00  --clausifier                            res/vclausify_rel
% 3.93/1.00  --clausifier_options                    ""
% 3.93/1.00  --stdin                                 false
% 3.93/1.00  --stats_out                             all
% 3.93/1.00  
% 3.93/1.00  ------ General Options
% 3.93/1.00  
% 3.93/1.00  --fof                                   false
% 3.93/1.00  --time_out_real                         305.
% 3.93/1.00  --time_out_virtual                      -1.
% 3.93/1.00  --symbol_type_check                     false
% 3.93/1.00  --clausify_out                          false
% 3.93/1.00  --sig_cnt_out                           false
% 3.93/1.00  --trig_cnt_out                          false
% 3.93/1.00  --trig_cnt_out_tolerance                1.
% 3.93/1.00  --trig_cnt_out_sk_spl                   false
% 3.93/1.00  --abstr_cl_out                          false
% 3.93/1.00  
% 3.93/1.00  ------ Global Options
% 3.93/1.00  
% 3.93/1.00  --schedule                              default
% 3.93/1.00  --add_important_lit                     false
% 3.93/1.00  --prop_solver_per_cl                    1000
% 3.93/1.00  --min_unsat_core                        false
% 3.93/1.00  --soft_assumptions                      false
% 3.93/1.00  --soft_lemma_size                       3
% 3.93/1.00  --prop_impl_unit_size                   0
% 3.93/1.00  --prop_impl_unit                        []
% 3.93/1.00  --share_sel_clauses                     true
% 3.93/1.00  --reset_solvers                         false
% 3.93/1.00  --bc_imp_inh                            [conj_cone]
% 3.93/1.00  --conj_cone_tolerance                   3.
% 3.93/1.00  --extra_neg_conj                        none
% 3.93/1.00  --large_theory_mode                     true
% 3.93/1.00  --prolific_symb_bound                   200
% 3.93/1.00  --lt_threshold                          2000
% 3.93/1.00  --clause_weak_htbl                      true
% 3.93/1.00  --gc_record_bc_elim                     false
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing Options
% 3.93/1.00  
% 3.93/1.00  --preprocessing_flag                    true
% 3.93/1.00  --time_out_prep_mult                    0.1
% 3.93/1.00  --splitting_mode                        input
% 3.93/1.00  --splitting_grd                         true
% 3.93/1.00  --splitting_cvd                         false
% 3.93/1.00  --splitting_cvd_svl                     false
% 3.93/1.00  --splitting_nvd                         32
% 3.93/1.00  --sub_typing                            true
% 3.93/1.00  --prep_gs_sim                           true
% 3.93/1.00  --prep_unflatten                        true
% 3.93/1.00  --prep_res_sim                          true
% 3.93/1.00  --prep_upred                            true
% 3.93/1.00  --prep_sem_filter                       exhaustive
% 3.93/1.00  --prep_sem_filter_out                   false
% 3.93/1.00  --pred_elim                             true
% 3.93/1.00  --res_sim_input                         true
% 3.93/1.00  --eq_ax_congr_red                       true
% 3.93/1.00  --pure_diseq_elim                       true
% 3.93/1.00  --brand_transform                       false
% 3.93/1.00  --non_eq_to_eq                          false
% 3.93/1.00  --prep_def_merge                        true
% 3.93/1.00  --prep_def_merge_prop_impl              false
% 3.93/1.00  --prep_def_merge_mbd                    true
% 3.93/1.00  --prep_def_merge_tr_red                 false
% 3.93/1.00  --prep_def_merge_tr_cl                  false
% 3.93/1.00  --smt_preprocessing                     true
% 3.93/1.00  --smt_ac_axioms                         fast
% 3.93/1.00  --preprocessed_out                      false
% 3.93/1.00  --preprocessed_stats                    false
% 3.93/1.00  
% 3.93/1.00  ------ Abstraction refinement Options
% 3.93/1.00  
% 3.93/1.00  --abstr_ref                             []
% 3.93/1.00  --abstr_ref_prep                        false
% 3.93/1.00  --abstr_ref_until_sat                   false
% 3.93/1.00  --abstr_ref_sig_restrict                funpre
% 3.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/1.00  --abstr_ref_under                       []
% 3.93/1.00  
% 3.93/1.00  ------ SAT Options
% 3.93/1.00  
% 3.93/1.00  --sat_mode                              false
% 3.93/1.00  --sat_fm_restart_options                ""
% 3.93/1.00  --sat_gr_def                            false
% 3.93/1.00  --sat_epr_types                         true
% 3.93/1.00  --sat_non_cyclic_types                  false
% 3.93/1.00  --sat_finite_models                     false
% 3.93/1.00  --sat_fm_lemmas                         false
% 3.93/1.00  --sat_fm_prep                           false
% 3.93/1.00  --sat_fm_uc_incr                        true
% 3.93/1.00  --sat_out_model                         small
% 3.93/1.00  --sat_out_clauses                       false
% 3.93/1.00  
% 3.93/1.00  ------ QBF Options
% 3.93/1.00  
% 3.93/1.00  --qbf_mode                              false
% 3.93/1.00  --qbf_elim_univ                         false
% 3.93/1.00  --qbf_dom_inst                          none
% 3.93/1.00  --qbf_dom_pre_inst                      false
% 3.93/1.00  --qbf_sk_in                             false
% 3.93/1.00  --qbf_pred_elim                         true
% 3.93/1.00  --qbf_split                             512
% 3.93/1.00  
% 3.93/1.00  ------ BMC1 Options
% 3.93/1.00  
% 3.93/1.00  --bmc1_incremental                      false
% 3.93/1.00  --bmc1_axioms                           reachable_all
% 3.93/1.00  --bmc1_min_bound                        0
% 3.93/1.00  --bmc1_max_bound                        -1
% 3.93/1.00  --bmc1_max_bound_default                -1
% 3.93/1.00  --bmc1_symbol_reachability              true
% 3.93/1.00  --bmc1_property_lemmas                  false
% 3.93/1.00  --bmc1_k_induction                      false
% 3.93/1.00  --bmc1_non_equiv_states                 false
% 3.93/1.00  --bmc1_deadlock                         false
% 3.93/1.00  --bmc1_ucm                              false
% 3.93/1.00  --bmc1_add_unsat_core                   none
% 3.93/1.00  --bmc1_unsat_core_children              false
% 3.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/1.00  --bmc1_out_stat                         full
% 3.93/1.00  --bmc1_ground_init                      false
% 3.93/1.00  --bmc1_pre_inst_next_state              false
% 3.93/1.00  --bmc1_pre_inst_state                   false
% 3.93/1.00  --bmc1_pre_inst_reach_state             false
% 3.93/1.00  --bmc1_out_unsat_core                   false
% 3.93/1.00  --bmc1_aig_witness_out                  false
% 3.93/1.00  --bmc1_verbose                          false
% 3.93/1.00  --bmc1_dump_clauses_tptp                false
% 3.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.93/1.00  --bmc1_dump_file                        -
% 3.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.93/1.00  --bmc1_ucm_extend_mode                  1
% 3.93/1.00  --bmc1_ucm_init_mode                    2
% 3.93/1.00  --bmc1_ucm_cone_mode                    none
% 3.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.93/1.00  --bmc1_ucm_relax_model                  4
% 3.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/1.00  --bmc1_ucm_layered_model                none
% 3.93/1.00  --bmc1_ucm_max_lemma_size               10
% 3.93/1.00  
% 3.93/1.00  ------ AIG Options
% 3.93/1.00  
% 3.93/1.00  --aig_mode                              false
% 3.93/1.00  
% 3.93/1.00  ------ Instantiation Options
% 3.93/1.00  
% 3.93/1.00  --instantiation_flag                    true
% 3.93/1.00  --inst_sos_flag                         true
% 3.93/1.00  --inst_sos_phase                        true
% 3.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/1.00  --inst_lit_sel_side                     none
% 3.93/1.00  --inst_solver_per_active                1400
% 3.93/1.00  --inst_solver_calls_frac                1.
% 3.93/1.00  --inst_passive_queue_type               priority_queues
% 3.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/1.00  --inst_passive_queues_freq              [25;2]
% 3.93/1.00  --inst_dismatching                      true
% 3.93/1.00  --inst_eager_unprocessed_to_passive     true
% 3.93/1.00  --inst_prop_sim_given                   true
% 3.93/1.00  --inst_prop_sim_new                     false
% 3.93/1.00  --inst_subs_new                         false
% 3.93/1.00  --inst_eq_res_simp                      false
% 3.93/1.00  --inst_subs_given                       false
% 3.93/1.00  --inst_orphan_elimination               true
% 3.93/1.00  --inst_learning_loop_flag               true
% 3.93/1.00  --inst_learning_start                   3000
% 3.93/1.00  --inst_learning_factor                  2
% 3.93/1.00  --inst_start_prop_sim_after_learn       3
% 3.93/1.00  --inst_sel_renew                        solver
% 3.93/1.00  --inst_lit_activity_flag                true
% 3.93/1.00  --inst_restr_to_given                   false
% 3.93/1.00  --inst_activity_threshold               500
% 3.93/1.00  --inst_out_proof                        true
% 3.93/1.00  
% 3.93/1.00  ------ Resolution Options
% 3.93/1.00  
% 3.93/1.00  --resolution_flag                       false
% 3.93/1.00  --res_lit_sel                           adaptive
% 3.93/1.00  --res_lit_sel_side                      none
% 3.93/1.00  --res_ordering                          kbo
% 3.93/1.00  --res_to_prop_solver                    active
% 3.93/1.00  --res_prop_simpl_new                    false
% 3.93/1.00  --res_prop_simpl_given                  true
% 3.93/1.00  --res_passive_queue_type                priority_queues
% 3.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/1.00  --res_passive_queues_freq               [15;5]
% 3.93/1.00  --res_forward_subs                      full
% 3.93/1.00  --res_backward_subs                     full
% 3.93/1.00  --res_forward_subs_resolution           true
% 3.93/1.00  --res_backward_subs_resolution          true
% 3.93/1.00  --res_orphan_elimination                true
% 3.93/1.00  --res_time_limit                        2.
% 3.93/1.00  --res_out_proof                         true
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Options
% 3.93/1.00  
% 3.93/1.00  --superposition_flag                    true
% 3.93/1.00  --sup_passive_queue_type                priority_queues
% 3.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.93/1.00  --demod_completeness_check              fast
% 3.93/1.00  --demod_use_ground                      true
% 3.93/1.00  --sup_to_prop_solver                    passive
% 3.93/1.00  --sup_prop_simpl_new                    true
% 3.93/1.00  --sup_prop_simpl_given                  true
% 3.93/1.00  --sup_fun_splitting                     true
% 3.93/1.00  --sup_smt_interval                      50000
% 3.93/1.00  
% 3.93/1.00  ------ Superposition Simplification Setup
% 3.93/1.00  
% 3.93/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.93/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.93/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.93/1.00  --sup_immed_triv                        [TrivRules]
% 3.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_immed_bw_main                     []
% 3.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/1.00  --sup_input_bw                          []
% 3.93/1.00  
% 3.93/1.00  ------ Combination Options
% 3.93/1.00  
% 3.93/1.00  --comb_res_mult                         3
% 3.93/1.00  --comb_sup_mult                         2
% 3.93/1.00  --comb_inst_mult                        10
% 3.93/1.00  
% 3.93/1.00  ------ Debug Options
% 3.93/1.00  
% 3.93/1.00  --dbg_backtrace                         false
% 3.93/1.00  --dbg_dump_prop_clauses                 false
% 3.93/1.00  --dbg_dump_prop_clauses_file            -
% 3.93/1.00  --dbg_out_stat                          false
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  ------ Proving...
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  % SZS status Theorem for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  fof(f19,conjecture,(
% 3.93/1.00    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f20,negated_conjecture,(
% 3.93/1.00    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.93/1.00    inference(negated_conjecture,[],[f19])).
% 3.93/1.00  
% 3.93/1.00  fof(f22,plain,(
% 3.93/1.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.93/1.00    inference(ennf_transformation,[],[f20])).
% 3.93/1.00  
% 3.93/1.00  fof(f25,plain,(
% 3.93/1.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 3.93/1.00    introduced(choice_axiom,[])).
% 3.93/1.00  
% 3.93/1.00  fof(f26,plain,(
% 3.93/1.00    (k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 3.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f25])).
% 3.93/1.00  
% 3.93/1.00  fof(f47,plain,(
% 3.93/1.00    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 3.93/1.00    inference(cnf_transformation,[],[f26])).
% 3.93/1.00  
% 3.93/1.00  fof(f18,axiom,(
% 3.93/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f46,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f18])).
% 3.93/1.00  
% 3.93/1.00  fof(f56,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.93/1.00    inference(definition_unfolding,[],[f46,f55])).
% 3.93/1.00  
% 3.93/1.00  fof(f10,axiom,(
% 3.93/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f36,plain,(
% 3.93/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f10])).
% 3.93/1.00  
% 3.93/1.00  fof(f11,axiom,(
% 3.93/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f37,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f11])).
% 3.93/1.00  
% 3.93/1.00  fof(f12,axiom,(
% 3.93/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f38,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f12])).
% 3.93/1.00  
% 3.93/1.00  fof(f13,axiom,(
% 3.93/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f39,plain,(
% 3.93/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f13])).
% 3.93/1.00  
% 3.93/1.00  fof(f14,axiom,(
% 3.93/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f40,plain,(
% 3.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f14])).
% 3.93/1.00  
% 3.93/1.00  fof(f15,axiom,(
% 3.93/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f41,plain,(
% 3.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f15])).
% 3.93/1.00  
% 3.93/1.00  fof(f16,axiom,(
% 3.93/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f42,plain,(
% 3.93/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f16])).
% 3.93/1.00  
% 3.93/1.00  fof(f51,plain,(
% 3.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.93/1.00    inference(definition_unfolding,[],[f41,f42])).
% 3.93/1.00  
% 3.93/1.00  fof(f52,plain,(
% 3.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.93/1.00    inference(definition_unfolding,[],[f40,f51])).
% 3.93/1.00  
% 3.93/1.00  fof(f53,plain,(
% 3.93/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.93/1.00    inference(definition_unfolding,[],[f39,f52])).
% 3.93/1.00  
% 3.93/1.00  fof(f54,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.93/1.00    inference(definition_unfolding,[],[f38,f53])).
% 3.93/1.00  
% 3.93/1.00  fof(f55,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.93/1.00    inference(definition_unfolding,[],[f37,f54])).
% 3.93/1.00  
% 3.93/1.00  fof(f59,plain,(
% 3.93/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.93/1.00    inference(definition_unfolding,[],[f36,f55])).
% 3.93/1.00  
% 3.93/1.00  fof(f69,plain,(
% 3.93/1.00    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 3.93/1.00    inference(definition_unfolding,[],[f47,f56,f59])).
% 3.93/1.00  
% 3.93/1.00  fof(f6,axiom,(
% 3.93/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f32,plain,(
% 3.93/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f6])).
% 3.93/1.00  
% 3.93/1.00  fof(f62,plain,(
% 3.93/1.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.93/1.00    inference(definition_unfolding,[],[f32,f56])).
% 3.93/1.00  
% 3.93/1.00  fof(f17,axiom,(
% 3.93/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f23,plain,(
% 3.93/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.93/1.00    inference(nnf_transformation,[],[f17])).
% 3.93/1.00  
% 3.93/1.00  fof(f24,plain,(
% 3.93/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.93/1.00    inference(flattening,[],[f23])).
% 3.93/1.00  
% 3.93/1.00  fof(f43,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f24])).
% 3.93/1.00  
% 3.93/1.00  fof(f65,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.93/1.00    inference(definition_unfolding,[],[f43,f59,f59])).
% 3.93/1.00  
% 3.93/1.00  fof(f4,axiom,(
% 3.93/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f30,plain,(
% 3.93/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f4])).
% 3.93/1.00  
% 3.93/1.00  fof(f1,axiom,(
% 3.93/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f27,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f1])).
% 3.93/1.00  
% 3.93/1.00  fof(f9,axiom,(
% 3.93/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f35,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.93/1.00    inference(cnf_transformation,[],[f9])).
% 3.93/1.00  
% 3.93/1.00  fof(f57,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.93/1.00    inference(definition_unfolding,[],[f35,f56])).
% 3.93/1.00  
% 3.93/1.00  fof(f58,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.93/1.00    inference(definition_unfolding,[],[f27,f57])).
% 3.93/1.00  
% 3.93/1.00  fof(f61,plain,(
% 3.93/1.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 3.93/1.00    inference(definition_unfolding,[],[f30,f58])).
% 3.93/1.00  
% 3.93/1.00  fof(f8,axiom,(
% 3.93/1.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f34,plain,(
% 3.93/1.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.93/1.00    inference(cnf_transformation,[],[f8])).
% 3.93/1.00  
% 3.93/1.00  fof(f7,axiom,(
% 3.93/1.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f33,plain,(
% 3.93/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f7])).
% 3.93/1.00  
% 3.93/1.00  fof(f5,axiom,(
% 3.93/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f31,plain,(
% 3.93/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.93/1.00    inference(cnf_transformation,[],[f5])).
% 3.93/1.00  
% 3.93/1.00  fof(f50,plain,(
% 3.93/1.00    k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1),
% 3.93/1.00    inference(cnf_transformation,[],[f26])).
% 3.93/1.00  
% 3.93/1.00  fof(f66,plain,(
% 3.93/1.00    k1_xboole_0 != sK2 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1),
% 3.93/1.00    inference(definition_unfolding,[],[f50,f59])).
% 3.93/1.00  
% 3.93/1.00  fof(f48,plain,(
% 3.93/1.00    k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1),
% 3.93/1.00    inference(cnf_transformation,[],[f26])).
% 3.93/1.00  
% 3.93/1.00  fof(f68,plain,(
% 3.93/1.00    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1),
% 3.93/1.00    inference(definition_unfolding,[],[f48,f59,f59])).
% 3.93/1.00  
% 3.93/1.00  fof(f49,plain,(
% 3.93/1.00    k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1),
% 3.93/1.00    inference(cnf_transformation,[],[f26])).
% 3.93/1.00  
% 3.93/1.00  fof(f67,plain,(
% 3.93/1.00    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 | k1_xboole_0 != sK1),
% 3.93/1.00    inference(definition_unfolding,[],[f49,f59])).
% 3.93/1.00  
% 3.93/1.00  fof(f3,axiom,(
% 3.93/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f29,plain,(
% 3.93/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f3])).
% 3.93/1.00  
% 3.93/1.00  fof(f2,axiom,(
% 3.93/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.93/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/1.00  
% 3.93/1.00  fof(f21,plain,(
% 3.93/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.93/1.00    inference(ennf_transformation,[],[f2])).
% 3.93/1.00  
% 3.93/1.00  fof(f28,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.93/1.00    inference(cnf_transformation,[],[f21])).
% 3.93/1.00  
% 3.93/1.00  fof(f60,plain,(
% 3.93/1.00    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.93/1.00    inference(definition_unfolding,[],[f28,f56])).
% 3.93/1.00  
% 3.93/1.00  cnf(c_13,negated_conjecture,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_4,plain,
% 3.93/1.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.93/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_279,plain,
% 3.93/1.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2228,plain,
% 3.93/1.00      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_13,c_279]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_9,plain,
% 3.93/1.00      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.93/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.93/1.00      | k1_xboole_0 = X0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_276,plain,
% 3.93/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 3.93/1.00      | k1_xboole_0 = X1
% 3.93/1.00      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2331,plain,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 3.93/1.00      | sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2228,c_276]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2,plain,
% 3.93/1.00      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_280,plain,
% 3.93/1.00      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_6,plain,
% 3.93/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_5,plain,
% 3.93/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.93/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_476,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_636,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(k1_xboole_0,X2) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_476,c_5]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_801,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k1_xboole_0,X2) ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_636,c_5]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_630,plain,
% 3.93/1.00      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_6,c_476]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.93/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_644,plain,
% 3.93/1.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_630,c_3]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_802,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_801,c_644]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_645,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_644,c_476]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1223,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_802,c_645]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1225,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X3,X2))) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_802,c_802]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1231,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X1,X2) ),
% 3.93/1.00      inference(splitting,
% 3.93/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.93/1.00                [c_1225]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1354,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,X1) = k5_xboole_0(X0,X1) ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_1223,c_1231]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2822,plain,
% 3.93/1.00      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_280,c_1354]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2823,plain,
% 3.93/1.00      ( r1_tarski(sP0_iProver_split(X0,k5_xboole_0(sP0_iProver_split(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) = iProver_top ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_2822,c_1354]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1224,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))),X3)) = k5_xboole_0(X2,X3) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_802,c_5]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1353,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1224,c_1231]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1356,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(X0,X1),X2)) = sP0_iProver_split(X1,X2) ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1354,c_1353]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1357,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(sP0_iProver_split(X0,X1),X2)) = sP0_iProver_split(X1,X2) ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1356,c_1354]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2824,plain,
% 3.93/1.00      ( r1_tarski(sP0_iProver_split(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))),X1) = iProver_top ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_2823,c_1354,c_1357]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2829,plain,
% 3.93/1.00      ( r1_tarski(sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_13,c_2824]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2335,plain,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
% 3.93/1.00      | sK1 = k1_xboole_0
% 3.93/1.00      | k1_xboole_0 = X0
% 3.93/1.00      | r1_tarski(X0,sK1) != iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2331,c_276]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3014,plain,
% 3.93/1.00      ( sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 3.93/1.00      | sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
% 3.93/1.00      | sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2829,c_2335]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3427,plain,
% 3.93/1.00      ( sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
% 3.93/1.00      | sK1 = k1_xboole_0
% 3.93/1.00      | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3014,c_2829]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_10,negated_conjecture,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
% 3.93/1.00      | k1_xboole_0 != sK2 ),
% 3.93/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2339,plain,
% 3.93/1.00      ( sK1 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2331,c_10]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_478,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_883,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_478,c_645]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_891,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_883,c_3]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_906,plain,
% 3.93/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_891,c_891]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1218,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X0,X2))) = X1 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_906,c_802]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1367,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(k5_xboole_0(X1,X2),k5_xboole_0(X0,X2))) = X1 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1218,c_1354]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1220,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_891,c_802]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1362,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X0,X2))) = sP0_iProver_split(X2,X1) ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1220,c_1354]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1363,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X0,X2))) = sP0_iProver_split(X2,X1) ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1362,c_1354]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1368,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,X0)) = X1 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1367,c_1354,c_1363]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3417,plain,
% 3.93/1.00      ( sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK2
% 3.93/1.00      | sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
% 3.93/1.00      | sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3014,c_1368]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2069,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,X0) = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1354,c_6]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3429,plain,
% 3.93/1.00      ( sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
% 3.93/1.00      | sK1 = k1_xboole_0
% 3.93/1.00      | sK2 = k1_xboole_0 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_3417,c_2069]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3531,plain,
% 3.93/1.00      ( sK1 = k1_xboole_0
% 3.93/1.00      | sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_3427,c_2339,c_3429]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3532,plain,
% 3.93/1.00      ( sP0_iProver_split(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
% 3.93/1.00      | sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(renaming,[status(thm)],[c_3531]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3533,plain,
% 3.93/1.00      ( sP0_iProver_split(sK2,sK1) = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2331,c_3532]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_12,negated_conjecture,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK1
% 3.93/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
% 3.93/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2337,plain,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
% 3.93/1.00      | sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_2331,c_12]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_11,negated_conjecture,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2
% 3.93/1.00      | k1_xboole_0 != sK1 ),
% 3.93/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_296,plain,
% 3.93/1.00      ( ~ r1_tarski(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 3.93/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK1
% 3.93/1.00      | k1_xboole_0 = sK1 ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_298,plain,
% 3.93/1.00      ( ~ r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.93/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK1
% 3.93/1.00      | k1_xboole_0 = sK1 ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_296]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_159,plain,( X0 = X0 ),theory(equality) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_375,plain,
% 3.93/1.00      ( sK1 = sK1 ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_159]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_163,plain,
% 3.93/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.93/1.00      theory(equality) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_422,plain,
% 3.93/1.00      ( r1_tarski(X0,X1)
% 3.93/1.00      | ~ r1_tarski(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
% 3.93/1.00      | X0 != X2
% 3.93/1.00      | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_163]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_650,plain,
% 3.93/1.00      ( r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.93/1.00      | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 3.93/1.00      | X0 != sK1
% 3.93/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_422]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_777,plain,
% 3.93/1.00      ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 3.93/1.00      | ~ r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 3.93/1.00      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 3.93/1.00      | sK1 != sK1 ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_650]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_514,plain,
% 3.93/1.00      ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_937,plain,
% 3.93/1.00      ( r1_tarski(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_514]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_2435,plain,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != sK2 ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_2337,c_13,c_12,c_11,c_298,c_375,c_777,c_937]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3542,plain,
% 3.93/1.00      ( sP0_iProver_split(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = sK2
% 3.93/1.00      | sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_3532,c_1368]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1213,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) = X1 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_6,c_802]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1372,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X0,k1_xboole_0))) = X1 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1213,c_1354]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1373,plain,
% 3.93/1.00      ( sP0_iProver_split(k1_xboole_0,X0) = X0 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1372,c_1354,c_1363]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_897,plain,
% 3.93/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_5,c_891]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1412,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,k5_xboole_0(X2,X0))) = sP0_iProver_split(X1,X2) ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_897,c_1354]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1413,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,sP0_iProver_split(X2,X0))) = sP0_iProver_split(X1,X2) ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_1412,c_1354]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1762,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,sP0_iProver_split(X1,X0)) = sP0_iProver_split(X1,k1_xboole_0) ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_1373,c_1413]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1766,plain,
% 3.93/1.00      ( sP0_iProver_split(X0,k1_xboole_0) = X0 ),
% 3.93/1.00      inference(light_normalisation,[status(thm)],[c_1762,c_1368]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3556,plain,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2
% 3.93/1.00      | sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_3542,c_1766]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3567,plain,
% 3.93/1.00      ( sK1 = k1_xboole_0 ),
% 3.93/1.00      inference(global_propositional_subsumption,
% 3.93/1.00                [status(thm)],
% 3.93/1.00                [c_3533,c_13,c_12,c_11,c_298,c_375,c_777,c_937,c_3556]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3576,plain,
% 3.93/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_3567,c_13]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_1,plain,
% 3.93/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.93/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_281,plain,
% 3.93/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_0,plain,
% 3.93/1.00      ( ~ r1_tarski(X0,X1)
% 3.93/1.00      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 3.93/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_282,plain,
% 3.93/1.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 3.93/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3017,plain,
% 3.93/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.93/1.00      inference(superposition,[status(thm)],[c_281,c_282]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_3578,plain,
% 3.93/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = sK2 ),
% 3.93/1.00      inference(demodulation,[status(thm)],[c_3576,c_3017]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(contradiction,plain,
% 3.93/1.00      ( $false ),
% 3.93/1.00      inference(minisat,[status(thm)],[c_3578,c_2435]) ).
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  ------                               Statistics
% 3.93/1.00  
% 3.93/1.00  ------ General
% 3.93/1.00  
% 3.93/1.00  abstr_ref_over_cycles:                  0
% 3.93/1.00  abstr_ref_under_cycles:                 0
% 3.93/1.00  gc_basic_clause_elim:                   0
% 3.93/1.00  forced_gc_time:                         0
% 3.93/1.00  parsing_time:                           0.017
% 3.93/1.00  unif_index_cands_time:                  0.
% 3.93/1.00  unif_index_add_time:                    0.
% 3.93/1.00  orderings_time:                         0.
% 3.93/1.00  out_proof_time:                         0.015
% 3.93/1.00  total_time:                             0.217
% 3.93/1.00  num_of_symbols:                         40
% 3.93/1.00  num_of_terms:                           5440
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing
% 3.93/1.00  
% 3.93/1.00  num_of_splits:                          0
% 3.93/1.00  num_of_split_atoms:                     1
% 3.93/1.00  num_of_reused_defs:                     0
% 3.93/1.00  num_eq_ax_congr_red:                    0
% 3.93/1.00  num_of_sem_filtered_clauses:            1
% 3.93/1.00  num_of_subtypes:                        0
% 3.93/1.00  monotx_restored_types:                  0
% 3.93/1.00  sat_num_of_epr_types:                   0
% 3.93/1.00  sat_num_of_non_cyclic_types:            0
% 3.93/1.00  sat_guarded_non_collapsed_types:        0
% 3.93/1.00  num_pure_diseq_elim:                    0
% 3.93/1.00  simp_replaced_by:                       0
% 3.93/1.00  res_preprocessed:                       55
% 3.93/1.00  prep_upred:                             0
% 3.93/1.00  prep_unflattend:                        17
% 3.93/1.00  smt_new_axioms:                         0
% 3.93/1.00  pred_elim_cands:                        1
% 3.93/1.00  pred_elim:                              0
% 3.93/1.00  pred_elim_cl:                           0
% 3.93/1.00  pred_elim_cycles:                       1
% 3.93/1.00  merged_defs:                            0
% 3.93/1.00  merged_defs_ncl:                        0
% 3.93/1.00  bin_hyper_res:                          0
% 3.93/1.00  prep_cycles:                            3
% 3.93/1.00  pred_elim_time:                         0.001
% 3.93/1.00  splitting_time:                         0.
% 3.93/1.00  sem_filter_time:                        0.
% 3.93/1.00  monotx_time:                            0.
% 3.93/1.00  subtype_inf_time:                       0.
% 3.93/1.00  
% 3.93/1.00  ------ Problem properties
% 3.93/1.00  
% 3.93/1.00  clauses:                                14
% 3.93/1.00  conjectures:                            4
% 3.93/1.00  epr:                                    1
% 3.93/1.00  horn:                                   13
% 3.93/1.00  ground:                                 4
% 3.93/1.00  unary:                                  9
% 3.93/1.00  binary:                                 4
% 3.93/1.00  lits:                                   20
% 3.93/1.00  lits_eq:                                13
% 3.93/1.00  fd_pure:                                0
% 3.93/1.00  fd_pseudo:                              0
% 3.93/1.00  fd_cond:                                0
% 3.93/1.00  fd_pseudo_cond:                         1
% 3.93/1.00  ac_symbols:                             2
% 3.93/1.00  
% 3.93/1.00  ------ Propositional Solver
% 3.93/1.00  
% 3.93/1.00  prop_solver_calls:                      25
% 3.93/1.00  prop_fast_solver_calls:                 309
% 3.93/1.00  smt_solver_calls:                       0
% 3.93/1.00  smt_fast_solver_calls:                  0
% 3.93/1.00  prop_num_of_clauses:                    1594
% 3.93/1.00  prop_preprocess_simplified:             4148
% 3.93/1.00  prop_fo_subsumed:                       3
% 3.93/1.00  prop_solver_time:                       0.
% 3.93/1.00  smt_solver_time:                        0.
% 3.93/1.00  smt_fast_solver_time:                   0.
% 3.93/1.00  prop_fast_solver_time:                  0.
% 3.93/1.00  prop_unsat_core_time:                   0.
% 3.93/1.00  
% 3.93/1.00  ------ QBF
% 3.93/1.00  
% 3.93/1.00  qbf_q_res:                              0
% 3.93/1.00  qbf_num_tautologies:                    0
% 3.93/1.00  qbf_prep_cycles:                        0
% 3.93/1.00  
% 3.93/1.00  ------ BMC1
% 3.93/1.00  
% 3.93/1.00  bmc1_current_bound:                     -1
% 3.93/1.00  bmc1_last_solved_bound:                 -1
% 3.93/1.00  bmc1_unsat_core_size:                   -1
% 3.93/1.00  bmc1_unsat_core_parents_size:           -1
% 3.93/1.00  bmc1_merge_next_fun:                    0
% 3.93/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.93/1.00  
% 3.93/1.00  ------ Instantiation
% 3.93/1.00  
% 3.93/1.00  inst_num_of_clauses:                    507
% 3.93/1.00  inst_num_in_passive:                    235
% 3.93/1.00  inst_num_in_active:                     226
% 3.93/1.00  inst_num_in_unprocessed:                46
% 3.93/1.00  inst_num_of_loops:                      260
% 3.93/1.00  inst_num_of_learning_restarts:          0
% 3.93/1.00  inst_num_moves_active_passive:          30
% 3.93/1.00  inst_lit_activity:                      0
% 3.93/1.00  inst_lit_activity_moves:                0
% 3.93/1.00  inst_num_tautologies:                   0
% 3.93/1.00  inst_num_prop_implied:                  0
% 3.93/1.00  inst_num_existing_simplified:           0
% 3.93/1.00  inst_num_eq_res_simplified:             0
% 3.93/1.00  inst_num_child_elim:                    0
% 3.93/1.00  inst_num_of_dismatching_blockings:      208
% 3.93/1.00  inst_num_of_non_proper_insts:           519
% 3.93/1.00  inst_num_of_duplicates:                 0
% 3.93/1.00  inst_inst_num_from_inst_to_res:         0
% 3.93/1.00  inst_dismatching_checking_time:         0.
% 3.93/1.00  
% 3.93/1.00  ------ Resolution
% 3.93/1.00  
% 3.93/1.00  res_num_of_clauses:                     0
% 3.93/1.00  res_num_in_passive:                     0
% 3.93/1.00  res_num_in_active:                      0
% 3.93/1.00  res_num_of_loops:                       58
% 3.93/1.00  res_forward_subset_subsumed:            74
% 3.93/1.00  res_backward_subset_subsumed:           0
% 3.93/1.00  res_forward_subsumed:                   1
% 3.93/1.00  res_backward_subsumed:                  0
% 3.93/1.00  res_forward_subsumption_resolution:     0
% 3.93/1.00  res_backward_subsumption_resolution:    0
% 3.93/1.00  res_clause_to_clause_subsumption:       898
% 3.93/1.00  res_orphan_elimination:                 0
% 3.93/1.00  res_tautology_del:                      44
% 3.93/1.00  res_num_eq_res_simplified:              0
% 3.93/1.00  res_num_sel_changes:                    0
% 3.93/1.00  res_moves_from_active_to_pass:          0
% 3.93/1.00  
% 3.93/1.00  ------ Superposition
% 3.93/1.00  
% 3.93/1.00  sup_time_total:                         0.
% 3.93/1.00  sup_time_generating:                    0.
% 3.93/1.00  sup_time_sim_full:                      0.
% 3.93/1.00  sup_time_sim_immed:                     0.
% 3.93/1.00  
% 3.93/1.00  sup_num_of_clauses:                     115
% 3.93/1.00  sup_num_in_active:                      22
% 3.93/1.00  sup_num_in_passive:                     93
% 3.93/1.00  sup_num_of_loops:                       51
% 3.93/1.00  sup_fw_superposition:                   241
% 3.93/1.00  sup_bw_superposition:                   243
% 3.93/1.00  sup_immediate_simplified:               121
% 3.93/1.00  sup_given_eliminated:                   4
% 3.93/1.00  comparisons_done:                       0
% 3.93/1.00  comparisons_avoided:                    6
% 3.93/1.00  
% 3.93/1.00  ------ Simplifications
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  sim_fw_subset_subsumed:                 0
% 3.93/1.00  sim_bw_subset_subsumed:                 8
% 3.93/1.00  sim_fw_subsumed:                        18
% 3.93/1.00  sim_bw_subsumed:                        4
% 3.93/1.00  sim_fw_subsumption_res:                 0
% 3.93/1.00  sim_bw_subsumption_res:                 0
% 3.93/1.00  sim_tautology_del:                      1
% 3.93/1.00  sim_eq_tautology_del:                   34
% 3.93/1.00  sim_eq_res_simp:                        0
% 3.93/1.00  sim_fw_demodulated:                     123
% 3.93/1.00  sim_bw_demodulated:                     34
% 3.93/1.00  sim_light_normalised:                   41
% 3.93/1.00  sim_joinable_taut:                      6
% 3.93/1.00  sim_joinable_simp:                      0
% 3.93/1.00  sim_ac_normalised:                      0
% 3.93/1.00  sim_smt_subsumption:                    0
% 3.93/1.00  
%------------------------------------------------------------------------------
