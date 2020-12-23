%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:02 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 224 expanded)
%              Number of clauses        :   29 (  30 expanded)
%              Number of leaves         :   17 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  174 ( 371 expanded)
%              Number of equality atoms :   93 ( 236 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f24])).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK0(X0,X1,X2))
        & r1_tarski(X2,sK0(X0,X1,X2))
        & r1_tarski(X0,sK0(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK0(X0,X1,X2))
        & r1_tarski(X2,sK0(X0,X1,X2))
        & r1_tarski(X0,sK0(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | r1_tarski(X0,sK0(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f46])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = X1
      | r1_tarski(X0,sK0(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X1,sK0(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = X1
      | ~ r1_tarski(X1,sK0(X0,X1,X2))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f48,f48])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f54,plain,(
    ! [X0,X1] : k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f32,f50,f49])).

fof(f42,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f44,plain,(
    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_274,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,sK0(X0,X1,X2))
    | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_276,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,sK0(X0,X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,sK0(X0,X1,X2))
    | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_278,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X2,sK0(X0,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_881,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_276,c_278])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2077,plain,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_26])).

cnf(c_2084,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_274,c_2077])).

cnf(c_7,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_384,plain,
    ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_273,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_275,plain,
    ( k7_relat_1(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_500,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
    inference(superposition,[status(thm)],[c_273,c_275])).

cnf(c_999,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK3,X1),X0) ),
    inference(superposition,[status(thm)],[c_7,c_500])).

cnf(c_1277,plain,
    ( k7_relat_1(k7_relat_1(sK3,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X1) = k7_relat_1(sK3,X1) ),
    inference(superposition,[status(thm)],[c_384,c_999])).

cnf(c_2302,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_2084,c_1277])).

cnf(c_128,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_456,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_129,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_363,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X0
    | k7_relat_1(sK3,sK1) != X0
    | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_455,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(sK3,sK1)
    | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_9,negated_conjecture,
    ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2302,c_456,c_455,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:12:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.45/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.45/0.99  
% 3.45/0.99  ------  iProver source info
% 3.45/0.99  
% 3.45/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.45/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.45/0.99  git: non_committed_changes: false
% 3.45/0.99  git: last_make_outside_of_git: false
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    --mode clausify
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             sel
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         604.99
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              none
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           false
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             false
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         false
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     num_symb
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       true
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     false
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   []
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_full_bw                           [BwDemod]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  ------ Parsing...
% 3.45/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.45/0.99  ------ Proving...
% 3.45/0.99  ------ Problem Properties 
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  clauses                                 11
% 3.45/0.99  conjectures                             3
% 3.45/0.99  EPR                                     4
% 3.45/0.99  Horn                                    9
% 3.45/0.99  unary                                   6
% 3.45/0.99  binary                                  1
% 3.45/0.99  lits                                    23
% 3.45/0.99  lits eq                                 8
% 3.45/0.99  fd_pure                                 0
% 3.45/0.99  fd_pseudo                               0
% 3.45/0.99  fd_cond                                 0
% 3.45/0.99  fd_pseudo_cond                          4
% 3.45/0.99  AC symbols                              0
% 3.45/0.99  
% 3.45/0.99  ------ Input Options Time Limit: Unbounded
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ 
% 3.45/0.99  Current options:
% 3.45/0.99  ------ 
% 3.45/0.99  
% 3.45/0.99  ------ Input Options
% 3.45/0.99  
% 3.45/0.99  --out_options                           all
% 3.45/0.99  --tptp_safe_out                         true
% 3.45/0.99  --problem_path                          ""
% 3.45/0.99  --include_path                          ""
% 3.45/0.99  --clausifier                            res/vclausify_rel
% 3.45/0.99  --clausifier_options                    --mode clausify
% 3.45/0.99  --stdin                                 false
% 3.45/0.99  --stats_out                             sel
% 3.45/0.99  
% 3.45/0.99  ------ General Options
% 3.45/0.99  
% 3.45/0.99  --fof                                   false
% 3.45/0.99  --time_out_real                         604.99
% 3.45/0.99  --time_out_virtual                      -1.
% 3.45/0.99  --symbol_type_check                     false
% 3.45/0.99  --clausify_out                          false
% 3.45/0.99  --sig_cnt_out                           false
% 3.45/0.99  --trig_cnt_out                          false
% 3.45/0.99  --trig_cnt_out_tolerance                1.
% 3.45/0.99  --trig_cnt_out_sk_spl                   false
% 3.45/0.99  --abstr_cl_out                          false
% 3.45/0.99  
% 3.45/0.99  ------ Global Options
% 3.45/0.99  
% 3.45/0.99  --schedule                              none
% 3.45/0.99  --add_important_lit                     false
% 3.45/0.99  --prop_solver_per_cl                    1000
% 3.45/0.99  --min_unsat_core                        false
% 3.45/0.99  --soft_assumptions                      false
% 3.45/0.99  --soft_lemma_size                       3
% 3.45/0.99  --prop_impl_unit_size                   0
% 3.45/0.99  --prop_impl_unit                        []
% 3.45/0.99  --share_sel_clauses                     true
% 3.45/0.99  --reset_solvers                         false
% 3.45/0.99  --bc_imp_inh                            [conj_cone]
% 3.45/0.99  --conj_cone_tolerance                   3.
% 3.45/0.99  --extra_neg_conj                        none
% 3.45/0.99  --large_theory_mode                     true
% 3.45/0.99  --prolific_symb_bound                   200
% 3.45/0.99  --lt_threshold                          2000
% 3.45/0.99  --clause_weak_htbl                      true
% 3.45/0.99  --gc_record_bc_elim                     false
% 3.45/0.99  
% 3.45/0.99  ------ Preprocessing Options
% 3.45/0.99  
% 3.45/0.99  --preprocessing_flag                    true
% 3.45/0.99  --time_out_prep_mult                    0.1
% 3.45/0.99  --splitting_mode                        input
% 3.45/0.99  --splitting_grd                         true
% 3.45/0.99  --splitting_cvd                         false
% 3.45/0.99  --splitting_cvd_svl                     false
% 3.45/0.99  --splitting_nvd                         32
% 3.45/0.99  --sub_typing                            true
% 3.45/0.99  --prep_gs_sim                           false
% 3.45/0.99  --prep_unflatten                        true
% 3.45/0.99  --prep_res_sim                          true
% 3.45/0.99  --prep_upred                            true
% 3.45/0.99  --prep_sem_filter                       exhaustive
% 3.45/0.99  --prep_sem_filter_out                   false
% 3.45/0.99  --pred_elim                             false
% 3.45/0.99  --res_sim_input                         true
% 3.45/0.99  --eq_ax_congr_red                       true
% 3.45/0.99  --pure_diseq_elim                       true
% 3.45/0.99  --brand_transform                       false
% 3.45/0.99  --non_eq_to_eq                          false
% 3.45/0.99  --prep_def_merge                        true
% 3.45/0.99  --prep_def_merge_prop_impl              false
% 3.45/0.99  --prep_def_merge_mbd                    true
% 3.45/0.99  --prep_def_merge_tr_red                 false
% 3.45/0.99  --prep_def_merge_tr_cl                  false
% 3.45/0.99  --smt_preprocessing                     true
% 3.45/0.99  --smt_ac_axioms                         fast
% 3.45/0.99  --preprocessed_out                      false
% 3.45/0.99  --preprocessed_stats                    false
% 3.45/0.99  
% 3.45/0.99  ------ Abstraction refinement Options
% 3.45/0.99  
% 3.45/0.99  --abstr_ref                             []
% 3.45/0.99  --abstr_ref_prep                        false
% 3.45/0.99  --abstr_ref_until_sat                   false
% 3.45/0.99  --abstr_ref_sig_restrict                funpre
% 3.45/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.45/0.99  --abstr_ref_under                       []
% 3.45/0.99  
% 3.45/0.99  ------ SAT Options
% 3.45/0.99  
% 3.45/0.99  --sat_mode                              false
% 3.45/0.99  --sat_fm_restart_options                ""
% 3.45/0.99  --sat_gr_def                            false
% 3.45/0.99  --sat_epr_types                         true
% 3.45/0.99  --sat_non_cyclic_types                  false
% 3.45/0.99  --sat_finite_models                     false
% 3.45/0.99  --sat_fm_lemmas                         false
% 3.45/0.99  --sat_fm_prep                           false
% 3.45/0.99  --sat_fm_uc_incr                        true
% 3.45/0.99  --sat_out_model                         small
% 3.45/0.99  --sat_out_clauses                       false
% 3.45/0.99  
% 3.45/0.99  ------ QBF Options
% 3.45/0.99  
% 3.45/0.99  --qbf_mode                              false
% 3.45/0.99  --qbf_elim_univ                         false
% 3.45/0.99  --qbf_dom_inst                          none
% 3.45/0.99  --qbf_dom_pre_inst                      false
% 3.45/0.99  --qbf_sk_in                             false
% 3.45/0.99  --qbf_pred_elim                         true
% 3.45/0.99  --qbf_split                             512
% 3.45/0.99  
% 3.45/0.99  ------ BMC1 Options
% 3.45/0.99  
% 3.45/0.99  --bmc1_incremental                      false
% 3.45/0.99  --bmc1_axioms                           reachable_all
% 3.45/0.99  --bmc1_min_bound                        0
% 3.45/0.99  --bmc1_max_bound                        -1
% 3.45/0.99  --bmc1_max_bound_default                -1
% 3.45/0.99  --bmc1_symbol_reachability              true
% 3.45/0.99  --bmc1_property_lemmas                  false
% 3.45/0.99  --bmc1_k_induction                      false
% 3.45/0.99  --bmc1_non_equiv_states                 false
% 3.45/0.99  --bmc1_deadlock                         false
% 3.45/0.99  --bmc1_ucm                              false
% 3.45/0.99  --bmc1_add_unsat_core                   none
% 3.45/0.99  --bmc1_unsat_core_children              false
% 3.45/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.45/0.99  --bmc1_out_stat                         full
% 3.45/0.99  --bmc1_ground_init                      false
% 3.45/0.99  --bmc1_pre_inst_next_state              false
% 3.45/0.99  --bmc1_pre_inst_state                   false
% 3.45/0.99  --bmc1_pre_inst_reach_state             false
% 3.45/0.99  --bmc1_out_unsat_core                   false
% 3.45/0.99  --bmc1_aig_witness_out                  false
% 3.45/0.99  --bmc1_verbose                          false
% 3.45/0.99  --bmc1_dump_clauses_tptp                false
% 3.45/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.45/0.99  --bmc1_dump_file                        -
% 3.45/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.45/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.45/0.99  --bmc1_ucm_extend_mode                  1
% 3.45/0.99  --bmc1_ucm_init_mode                    2
% 3.45/0.99  --bmc1_ucm_cone_mode                    none
% 3.45/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.45/0.99  --bmc1_ucm_relax_model                  4
% 3.45/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.45/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.45/0.99  --bmc1_ucm_layered_model                none
% 3.45/0.99  --bmc1_ucm_max_lemma_size               10
% 3.45/0.99  
% 3.45/0.99  ------ AIG Options
% 3.45/0.99  
% 3.45/0.99  --aig_mode                              false
% 3.45/0.99  
% 3.45/0.99  ------ Instantiation Options
% 3.45/0.99  
% 3.45/0.99  --instantiation_flag                    true
% 3.45/0.99  --inst_sos_flag                         false
% 3.45/0.99  --inst_sos_phase                        true
% 3.45/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.45/0.99  --inst_lit_sel_side                     num_symb
% 3.45/0.99  --inst_solver_per_active                1400
% 3.45/0.99  --inst_solver_calls_frac                1.
% 3.45/0.99  --inst_passive_queue_type               priority_queues
% 3.45/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.45/0.99  --inst_passive_queues_freq              [25;2]
% 3.45/0.99  --inst_dismatching                      true
% 3.45/0.99  --inst_eager_unprocessed_to_passive     true
% 3.45/0.99  --inst_prop_sim_given                   true
% 3.45/0.99  --inst_prop_sim_new                     false
% 3.45/0.99  --inst_subs_new                         false
% 3.45/0.99  --inst_eq_res_simp                      false
% 3.45/0.99  --inst_subs_given                       false
% 3.45/0.99  --inst_orphan_elimination               true
% 3.45/0.99  --inst_learning_loop_flag               true
% 3.45/0.99  --inst_learning_start                   3000
% 3.45/0.99  --inst_learning_factor                  2
% 3.45/0.99  --inst_start_prop_sim_after_learn       3
% 3.45/0.99  --inst_sel_renew                        solver
% 3.45/0.99  --inst_lit_activity_flag                true
% 3.45/0.99  --inst_restr_to_given                   false
% 3.45/0.99  --inst_activity_threshold               500
% 3.45/0.99  --inst_out_proof                        true
% 3.45/0.99  
% 3.45/0.99  ------ Resolution Options
% 3.45/0.99  
% 3.45/0.99  --resolution_flag                       true
% 3.45/0.99  --res_lit_sel                           adaptive
% 3.45/0.99  --res_lit_sel_side                      none
% 3.45/0.99  --res_ordering                          kbo
% 3.45/0.99  --res_to_prop_solver                    active
% 3.45/0.99  --res_prop_simpl_new                    false
% 3.45/0.99  --res_prop_simpl_given                  true
% 3.45/0.99  --res_passive_queue_type                priority_queues
% 3.45/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.45/0.99  --res_passive_queues_freq               [15;5]
% 3.45/0.99  --res_forward_subs                      full
% 3.45/0.99  --res_backward_subs                     full
% 3.45/0.99  --res_forward_subs_resolution           true
% 3.45/0.99  --res_backward_subs_resolution          true
% 3.45/0.99  --res_orphan_elimination                true
% 3.45/0.99  --res_time_limit                        2.
% 3.45/0.99  --res_out_proof                         true
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Options
% 3.45/0.99  
% 3.45/0.99  --superposition_flag                    true
% 3.45/0.99  --sup_passive_queue_type                priority_queues
% 3.45/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.45/0.99  --sup_passive_queues_freq               [1;4]
% 3.45/0.99  --demod_completeness_check              fast
% 3.45/0.99  --demod_use_ground                      true
% 3.45/0.99  --sup_to_prop_solver                    passive
% 3.45/0.99  --sup_prop_simpl_new                    true
% 3.45/0.99  --sup_prop_simpl_given                  true
% 3.45/0.99  --sup_fun_splitting                     false
% 3.45/0.99  --sup_smt_interval                      50000
% 3.45/0.99  
% 3.45/0.99  ------ Superposition Simplification Setup
% 3.45/0.99  
% 3.45/0.99  --sup_indices_passive                   []
% 3.45/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.45/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.45/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_full_bw                           [BwDemod]
% 3.45/0.99  --sup_immed_triv                        [TrivRules]
% 3.45/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.45/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_immed_bw_main                     []
% 3.45/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.45/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.45/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.45/0.99  
% 3.45/0.99  ------ Combination Options
% 3.45/0.99  
% 3.45/0.99  --comb_res_mult                         3
% 3.45/0.99  --comb_sup_mult                         2
% 3.45/0.99  --comb_inst_mult                        10
% 3.45/0.99  
% 3.45/0.99  ------ Debug Options
% 3.45/0.99  
% 3.45/0.99  --dbg_backtrace                         false
% 3.45/0.99  --dbg_dump_prop_clauses                 false
% 3.45/0.99  --dbg_dump_prop_clauses_file            -
% 3.45/0.99  --dbg_out_stat                          false
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  ------ Proving...
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS status Theorem for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  fof(f13,conjecture,(
% 3.45/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f14,negated_conjecture,(
% 3.45/0.99    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 3.45/0.99    inference(negated_conjecture,[],[f13])).
% 3.45/0.99  
% 3.45/0.99  fof(f18,plain,(
% 3.45/0.99    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.45/0.99    inference(ennf_transformation,[],[f14])).
% 3.45/0.99  
% 3.45/0.99  fof(f19,plain,(
% 3.45/0.99    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.45/0.99    inference(flattening,[],[f18])).
% 3.45/0.99  
% 3.45/0.99  fof(f24,plain,(
% 3.45/0.99    ? [X0,X1,X2] : (k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f25,plain,(
% 3.45/0.99    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) & r1_tarski(sK1,sK2) & v1_relat_1(sK3)),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f24])).
% 3.45/0.99  
% 3.45/0.99  fof(f43,plain,(
% 3.45/0.99    r1_tarski(sK1,sK2)),
% 3.45/0.99    inference(cnf_transformation,[],[f25])).
% 3.45/0.99  
% 3.45/0.99  fof(f2,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f15,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.45/0.99    inference(ennf_transformation,[],[f2])).
% 3.45/0.99  
% 3.45/0.99  fof(f16,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.45/0.99    inference(flattening,[],[f15])).
% 3.45/0.99  
% 3.45/0.99  fof(f22,plain,(
% 3.45/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK0(X0,X1,X2)) & r1_tarski(X2,sK0(X0,X1,X2)) & r1_tarski(X0,sK0(X0,X1,X2))))),
% 3.45/0.99    introduced(choice_axiom,[])).
% 3.45/0.99  
% 3.45/0.99  fof(f23,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK0(X0,X1,X2)) & r1_tarski(X2,sK0(X0,X1,X2)) & r1_tarski(X0,sK0(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.45/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).
% 3.45/0.99  
% 3.45/0.99  fof(f29,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | r1_tarski(X0,sK0(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f23])).
% 3.45/0.99  
% 3.45/0.99  fof(f10,axiom,(
% 3.45/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f39,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f10])).
% 3.45/0.99  
% 3.45/0.99  fof(f5,axiom,(
% 3.45/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f34,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f5])).
% 3.45/0.99  
% 3.45/0.99  fof(f6,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f35,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f6])).
% 3.45/0.99  
% 3.45/0.99  fof(f7,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f36,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f7])).
% 3.45/0.99  
% 3.45/0.99  fof(f8,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f37,plain,(
% 3.45/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f8])).
% 3.45/0.99  
% 3.45/0.99  fof(f9,axiom,(
% 3.45/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f38,plain,(
% 3.45/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f9])).
% 3.45/0.99  
% 3.45/0.99  fof(f45,plain,(
% 3.45/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f37,f38])).
% 3.45/0.99  
% 3.45/0.99  fof(f46,plain,(
% 3.45/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f36,f45])).
% 3.45/0.99  
% 3.45/0.99  fof(f47,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f35,f46])).
% 3.45/0.99  
% 3.45/0.99  fof(f48,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f34,f47])).
% 3.45/0.99  
% 3.45/0.99  fof(f49,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.45/0.99    inference(definition_unfolding,[],[f39,f48])).
% 3.45/0.99  
% 3.45/0.99  fof(f53,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = X1 | r1_tarski(X0,sK0(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f29,f49])).
% 3.45/0.99  
% 3.45/0.99  fof(f31,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X1,sK0(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f23])).
% 3.45/0.99  
% 3.45/0.99  fof(f51,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = X1 | ~r1_tarski(X1,sK0(X0,X1,X2)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f31,f49])).
% 3.45/0.99  
% 3.45/0.99  fof(f1,axiom,(
% 3.45/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f20,plain,(
% 3.45/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/0.99    inference(nnf_transformation,[],[f1])).
% 3.45/0.99  
% 3.45/0.99  fof(f21,plain,(
% 3.45/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.45/0.99    inference(flattening,[],[f20])).
% 3.45/0.99  
% 3.45/0.99  fof(f26,plain,(
% 3.45/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.45/0.99    inference(cnf_transformation,[],[f21])).
% 3.45/0.99  
% 3.45/0.99  fof(f58,plain,(
% 3.45/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.45/0.99    inference(equality_resolution,[],[f26])).
% 3.45/0.99  
% 3.45/0.99  fof(f4,axiom,(
% 3.45/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f33,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f4])).
% 3.45/0.99  
% 3.45/0.99  fof(f55,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f33,f48,f48])).
% 3.45/0.99  
% 3.45/0.99  fof(f3,axiom,(
% 3.45/0.99    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f32,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.45/0.99    inference(cnf_transformation,[],[f3])).
% 3.45/0.99  
% 3.45/0.99  fof(f11,axiom,(
% 3.45/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f40,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.45/0.99    inference(cnf_transformation,[],[f11])).
% 3.45/0.99  
% 3.45/0.99  fof(f50,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 3.45/0.99    inference(definition_unfolding,[],[f40,f48])).
% 3.45/0.99  
% 3.45/0.99  fof(f54,plain,(
% 3.45/0.99    ( ! [X0,X1] : (k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) = X0) )),
% 3.45/0.99    inference(definition_unfolding,[],[f32,f50,f49])).
% 3.45/0.99  
% 3.45/0.99  fof(f42,plain,(
% 3.45/0.99    v1_relat_1(sK3)),
% 3.45/0.99    inference(cnf_transformation,[],[f25])).
% 3.45/0.99  
% 3.45/0.99  fof(f12,axiom,(
% 3.45/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.45/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.45/0.99  
% 3.45/0.99  fof(f17,plain,(
% 3.45/0.99    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.45/0.99    inference(ennf_transformation,[],[f12])).
% 3.45/0.99  
% 3.45/0.99  fof(f41,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.45/0.99    inference(cnf_transformation,[],[f17])).
% 3.45/0.99  
% 3.45/0.99  fof(f56,plain,(
% 3.45/0.99    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 3.45/0.99    inference(definition_unfolding,[],[f41,f50])).
% 3.45/0.99  
% 3.45/0.99  fof(f44,plain,(
% 3.45/0.99    k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 3.45/0.99    inference(cnf_transformation,[],[f25])).
% 3.45/0.99  
% 3.45/0.99  cnf(c_10,negated_conjecture,
% 3.45/0.99      ( r1_tarski(sK1,sK2) ),
% 3.45/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_274,plain,
% 3.45/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_5,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,X1)
% 3.45/0.99      | ~ r1_tarski(X2,X1)
% 3.45/0.99      | r1_tarski(X0,sK0(X0,X1,X2))
% 3.45/0.99      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = X1 ),
% 3.45/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_276,plain,
% 3.45/0.99      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X2
% 3.45/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.45/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.45/0.99      | r1_tarski(X0,sK0(X0,X2,X1)) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_3,plain,
% 3.45/0.99      ( ~ r1_tarski(X0,X1)
% 3.45/0.99      | ~ r1_tarski(X2,X1)
% 3.45/0.99      | ~ r1_tarski(X1,sK0(X0,X1,X2))
% 3.45/0.99      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)) = X1 ),
% 3.45/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_278,plain,
% 3.45/0.99      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X2
% 3.45/0.99      | r1_tarski(X0,X2) != iProver_top
% 3.45/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.45/0.99      | r1_tarski(X2,sK0(X0,X2,X1)) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_881,plain,
% 3.45/0.99      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X0
% 3.45/0.99      | r1_tarski(X0,X0) != iProver_top
% 3.45/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_276,c_278]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2,plain,
% 3.45/0.99      ( r1_tarski(X0,X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_26,plain,
% 3.45/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2077,plain,
% 3.45/0.99      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X0
% 3.45/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.45/0.99      inference(global_propositional_subsumption,
% 3.45/0.99                [status(thm)],
% 3.45/0.99                [c_881,c_26]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2084,plain,
% 3.45/0.99      ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = sK2 ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_274,c_2077]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_7,plain,
% 3.45/0.99      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
% 3.45/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_6,plain,
% 3.45/0.99      ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
% 3.45/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_384,plain,
% 3.45/0.99      ( k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))) = X0 ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_11,negated_conjecture,
% 3.45/0.99      ( v1_relat_1(sK3) ),
% 3.45/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_273,plain,
% 3.45/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_8,plain,
% 3.45/0.99      ( ~ v1_relat_1(X0)
% 3.45/0.99      | k7_relat_1(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.45/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_275,plain,
% 3.45/0.99      ( k7_relat_1(X0,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 3.45/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.45/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_500,plain,
% 3.45/0.99      ( k7_relat_1(sK3,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_273,c_275]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_999,plain,
% 3.45/0.99      ( k7_relat_1(sK3,k1_setfam_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(sK3,X1),X0) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_7,c_500]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_1277,plain,
% 3.45/0.99      ( k7_relat_1(k7_relat_1(sK3,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X1) = k7_relat_1(sK3,X1) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_384,c_999]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_2302,plain,
% 3.45/0.99      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) = k7_relat_1(sK3,sK1) ),
% 3.45/0.99      inference(superposition,[status(thm)],[c_2084,c_1277]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_128,plain,( X0 = X0 ),theory(equality) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_456,plain,
% 3.45/0.99      ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,sK1) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_128]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_129,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_363,plain,
% 3.45/0.99      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != X0
% 3.45/0.99      | k7_relat_1(sK3,sK1) != X0
% 3.45/0.99      | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_129]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_455,plain,
% 3.45/0.99      ( k7_relat_1(k7_relat_1(sK3,sK2),sK1) != k7_relat_1(sK3,sK1)
% 3.45/0.99      | k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
% 3.45/0.99      | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1) ),
% 3.45/0.99      inference(instantiation,[status(thm)],[c_363]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(c_9,negated_conjecture,
% 3.45/0.99      ( k7_relat_1(sK3,sK1) != k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
% 3.45/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.45/0.99  
% 3.45/0.99  cnf(contradiction,plain,
% 3.45/0.99      ( $false ),
% 3.45/0.99      inference(minisat,[status(thm)],[c_2302,c_456,c_455,c_9]) ).
% 3.45/0.99  
% 3.45/0.99  
% 3.45/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.45/0.99  
% 3.45/0.99  ------                               Statistics
% 3.45/0.99  
% 3.45/0.99  ------ Selected
% 3.45/0.99  
% 3.45/0.99  total_time:                             0.12
% 3.45/0.99  
%------------------------------------------------------------------------------
