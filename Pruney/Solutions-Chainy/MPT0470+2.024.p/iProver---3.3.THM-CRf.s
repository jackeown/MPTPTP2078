%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:58 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 260 expanded)
%              Number of clauses        :   59 (  94 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  232 ( 484 expanded)
%              Number of equality atoms :  131 ( 273 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f30,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f33])).

fof(f56,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f63,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f61])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_442,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_454,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_447,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_910,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_447])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_446,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_445,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1286,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_445])).

cnf(c_2968,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_910,c_1286])).

cnf(c_7431,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_442,c_2968])).

cnf(c_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_443,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_602,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_443])).

cnf(c_31,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_33,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_50,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1291,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_33,c_50])).

cnf(c_1292,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1291])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_450,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_452,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1140,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_452])).

cnf(c_1580,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_1140])).

cnf(c_4755,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_442,c_1580])).

cnf(c_7446,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7431,c_4755])).

cnf(c_5,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_449,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_453,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1033,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_449,c_453])).

cnf(c_1908,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_1033])).

cnf(c_7447,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7446,c_5,c_1908])).

cnf(c_2967,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) = k5_relat_1(X0,sK0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_442,c_1286])).

cnf(c_6653,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_910,c_2967])).

cnf(c_15,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_444,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_903,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_444])).

cnf(c_1450,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_903,c_33,c_50])).

cnf(c_1451,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1450])).

cnf(c_1581,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_1140])).

cnf(c_5143,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_442,c_1581])).

cnf(c_6665,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_6653,c_5143])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_448,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1014,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_453])).

cnf(c_1686,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_1014])).

cnf(c_6666,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6665,c_5,c_1686])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6838,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6666,c_16])).

cnf(c_6839,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6838])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7447,c_6839])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:12:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.56/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/1.00  
% 3.56/1.00  ------  iProver source info
% 3.56/1.00  
% 3.56/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.56/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/1.00  git: non_committed_changes: false
% 3.56/1.00  git: last_make_outside_of_git: false
% 3.56/1.00  
% 3.56/1.00  ------ 
% 3.56/1.00  
% 3.56/1.00  ------ Input Options
% 3.56/1.00  
% 3.56/1.00  --out_options                           all
% 3.56/1.00  --tptp_safe_out                         true
% 3.56/1.00  --problem_path                          ""
% 3.56/1.00  --include_path                          ""
% 3.56/1.00  --clausifier                            res/vclausify_rel
% 3.56/1.00  --clausifier_options                    --mode clausify
% 3.56/1.00  --stdin                                 false
% 3.56/1.00  --stats_out                             sel
% 3.56/1.00  
% 3.56/1.00  ------ General Options
% 3.56/1.00  
% 3.56/1.00  --fof                                   false
% 3.56/1.00  --time_out_real                         604.99
% 3.56/1.00  --time_out_virtual                      -1.
% 3.56/1.00  --symbol_type_check                     false
% 3.56/1.00  --clausify_out                          false
% 3.56/1.00  --sig_cnt_out                           false
% 3.56/1.00  --trig_cnt_out                          false
% 3.56/1.00  --trig_cnt_out_tolerance                1.
% 3.56/1.00  --trig_cnt_out_sk_spl                   false
% 3.56/1.00  --abstr_cl_out                          false
% 3.56/1.00  
% 3.56/1.00  ------ Global Options
% 3.56/1.00  
% 3.56/1.00  --schedule                              none
% 3.56/1.00  --add_important_lit                     false
% 3.56/1.00  --prop_solver_per_cl                    1000
% 3.56/1.00  --min_unsat_core                        false
% 3.56/1.00  --soft_assumptions                      false
% 3.56/1.00  --soft_lemma_size                       3
% 3.56/1.00  --prop_impl_unit_size                   0
% 3.56/1.00  --prop_impl_unit                        []
% 3.56/1.00  --share_sel_clauses                     true
% 3.56/1.00  --reset_solvers                         false
% 3.56/1.00  --bc_imp_inh                            [conj_cone]
% 3.56/1.00  --conj_cone_tolerance                   3.
% 3.56/1.00  --extra_neg_conj                        none
% 3.56/1.00  --large_theory_mode                     true
% 3.56/1.00  --prolific_symb_bound                   200
% 3.56/1.00  --lt_threshold                          2000
% 3.56/1.00  --clause_weak_htbl                      true
% 3.56/1.00  --gc_record_bc_elim                     false
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing Options
% 3.56/1.00  
% 3.56/1.00  --preprocessing_flag                    true
% 3.56/1.00  --time_out_prep_mult                    0.1
% 3.56/1.00  --splitting_mode                        input
% 3.56/1.00  --splitting_grd                         true
% 3.56/1.00  --splitting_cvd                         false
% 3.56/1.00  --splitting_cvd_svl                     false
% 3.56/1.00  --splitting_nvd                         32
% 3.56/1.00  --sub_typing                            true
% 3.56/1.00  --prep_gs_sim                           false
% 3.56/1.00  --prep_unflatten                        true
% 3.56/1.00  --prep_res_sim                          true
% 3.56/1.00  --prep_upred                            true
% 3.56/1.00  --prep_sem_filter                       exhaustive
% 3.56/1.00  --prep_sem_filter_out                   false
% 3.56/1.00  --pred_elim                             false
% 3.56/1.00  --res_sim_input                         true
% 3.56/1.00  --eq_ax_congr_red                       true
% 3.56/1.00  --pure_diseq_elim                       true
% 3.56/1.00  --brand_transform                       false
% 3.56/1.00  --non_eq_to_eq                          false
% 3.56/1.00  --prep_def_merge                        true
% 3.56/1.00  --prep_def_merge_prop_impl              false
% 3.56/1.00  --prep_def_merge_mbd                    true
% 3.56/1.00  --prep_def_merge_tr_red                 false
% 3.56/1.00  --prep_def_merge_tr_cl                  false
% 3.56/1.00  --smt_preprocessing                     true
% 3.56/1.00  --smt_ac_axioms                         fast
% 3.56/1.00  --preprocessed_out                      false
% 3.56/1.00  --preprocessed_stats                    false
% 3.56/1.00  
% 3.56/1.00  ------ Abstraction refinement Options
% 3.56/1.00  
% 3.56/1.00  --abstr_ref                             []
% 3.56/1.00  --abstr_ref_prep                        false
% 3.56/1.00  --abstr_ref_until_sat                   false
% 3.56/1.00  --abstr_ref_sig_restrict                funpre
% 3.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/1.00  --abstr_ref_under                       []
% 3.56/1.00  
% 3.56/1.00  ------ SAT Options
% 3.56/1.00  
% 3.56/1.00  --sat_mode                              false
% 3.56/1.00  --sat_fm_restart_options                ""
% 3.56/1.00  --sat_gr_def                            false
% 3.56/1.00  --sat_epr_types                         true
% 3.56/1.00  --sat_non_cyclic_types                  false
% 3.56/1.00  --sat_finite_models                     false
% 3.56/1.00  --sat_fm_lemmas                         false
% 3.56/1.00  --sat_fm_prep                           false
% 3.56/1.00  --sat_fm_uc_incr                        true
% 3.56/1.00  --sat_out_model                         small
% 3.56/1.00  --sat_out_clauses                       false
% 3.56/1.00  
% 3.56/1.00  ------ QBF Options
% 3.56/1.00  
% 3.56/1.00  --qbf_mode                              false
% 3.56/1.00  --qbf_elim_univ                         false
% 3.56/1.00  --qbf_dom_inst                          none
% 3.56/1.00  --qbf_dom_pre_inst                      false
% 3.56/1.00  --qbf_sk_in                             false
% 3.56/1.00  --qbf_pred_elim                         true
% 3.56/1.00  --qbf_split                             512
% 3.56/1.00  
% 3.56/1.00  ------ BMC1 Options
% 3.56/1.00  
% 3.56/1.00  --bmc1_incremental                      false
% 3.56/1.00  --bmc1_axioms                           reachable_all
% 3.56/1.00  --bmc1_min_bound                        0
% 3.56/1.00  --bmc1_max_bound                        -1
% 3.56/1.00  --bmc1_max_bound_default                -1
% 3.56/1.00  --bmc1_symbol_reachability              true
% 3.56/1.00  --bmc1_property_lemmas                  false
% 3.56/1.00  --bmc1_k_induction                      false
% 3.56/1.00  --bmc1_non_equiv_states                 false
% 3.56/1.00  --bmc1_deadlock                         false
% 3.56/1.00  --bmc1_ucm                              false
% 3.56/1.00  --bmc1_add_unsat_core                   none
% 3.56/1.00  --bmc1_unsat_core_children              false
% 3.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/1.00  --bmc1_out_stat                         full
% 3.56/1.00  --bmc1_ground_init                      false
% 3.56/1.00  --bmc1_pre_inst_next_state              false
% 3.56/1.00  --bmc1_pre_inst_state                   false
% 3.56/1.00  --bmc1_pre_inst_reach_state             false
% 3.56/1.00  --bmc1_out_unsat_core                   false
% 3.56/1.00  --bmc1_aig_witness_out                  false
% 3.56/1.00  --bmc1_verbose                          false
% 3.56/1.00  --bmc1_dump_clauses_tptp                false
% 3.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.56/1.00  --bmc1_dump_file                        -
% 3.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.56/1.00  --bmc1_ucm_extend_mode                  1
% 3.56/1.00  --bmc1_ucm_init_mode                    2
% 3.56/1.00  --bmc1_ucm_cone_mode                    none
% 3.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.56/1.00  --bmc1_ucm_relax_model                  4
% 3.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/1.00  --bmc1_ucm_layered_model                none
% 3.56/1.00  --bmc1_ucm_max_lemma_size               10
% 3.56/1.00  
% 3.56/1.00  ------ AIG Options
% 3.56/1.00  
% 3.56/1.00  --aig_mode                              false
% 3.56/1.00  
% 3.56/1.00  ------ Instantiation Options
% 3.56/1.00  
% 3.56/1.00  --instantiation_flag                    true
% 3.56/1.00  --inst_sos_flag                         false
% 3.56/1.00  --inst_sos_phase                        true
% 3.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/1.00  --inst_lit_sel_side                     num_symb
% 3.56/1.00  --inst_solver_per_active                1400
% 3.56/1.00  --inst_solver_calls_frac                1.
% 3.56/1.00  --inst_passive_queue_type               priority_queues
% 3.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/1.00  --inst_passive_queues_freq              [25;2]
% 3.56/1.00  --inst_dismatching                      true
% 3.56/1.00  --inst_eager_unprocessed_to_passive     true
% 3.56/1.00  --inst_prop_sim_given                   true
% 3.56/1.00  --inst_prop_sim_new                     false
% 3.56/1.00  --inst_subs_new                         false
% 3.56/1.00  --inst_eq_res_simp                      false
% 3.56/1.00  --inst_subs_given                       false
% 3.56/1.00  --inst_orphan_elimination               true
% 3.56/1.00  --inst_learning_loop_flag               true
% 3.56/1.00  --inst_learning_start                   3000
% 3.56/1.00  --inst_learning_factor                  2
% 3.56/1.00  --inst_start_prop_sim_after_learn       3
% 3.56/1.00  --inst_sel_renew                        solver
% 3.56/1.00  --inst_lit_activity_flag                true
% 3.56/1.00  --inst_restr_to_given                   false
% 3.56/1.00  --inst_activity_threshold               500
% 3.56/1.00  --inst_out_proof                        true
% 3.56/1.00  
% 3.56/1.00  ------ Resolution Options
% 3.56/1.00  
% 3.56/1.00  --resolution_flag                       true
% 3.56/1.00  --res_lit_sel                           adaptive
% 3.56/1.00  --res_lit_sel_side                      none
% 3.56/1.00  --res_ordering                          kbo
% 3.56/1.00  --res_to_prop_solver                    active
% 3.56/1.00  --res_prop_simpl_new                    false
% 3.56/1.00  --res_prop_simpl_given                  true
% 3.56/1.00  --res_passive_queue_type                priority_queues
% 3.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/1.00  --res_passive_queues_freq               [15;5]
% 3.56/1.00  --res_forward_subs                      full
% 3.56/1.00  --res_backward_subs                     full
% 3.56/1.00  --res_forward_subs_resolution           true
% 3.56/1.00  --res_backward_subs_resolution          true
% 3.56/1.00  --res_orphan_elimination                true
% 3.56/1.00  --res_time_limit                        2.
% 3.56/1.00  --res_out_proof                         true
% 3.56/1.00  
% 3.56/1.00  ------ Superposition Options
% 3.56/1.00  
% 3.56/1.00  --superposition_flag                    true
% 3.56/1.00  --sup_passive_queue_type                priority_queues
% 3.56/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/1.00  --sup_passive_queues_freq               [1;4]
% 3.56/1.00  --demod_completeness_check              fast
% 3.56/1.00  --demod_use_ground                      true
% 3.56/1.00  --sup_to_prop_solver                    passive
% 3.56/1.00  --sup_prop_simpl_new                    true
% 3.56/1.00  --sup_prop_simpl_given                  true
% 3.56/1.00  --sup_fun_splitting                     false
% 3.56/1.00  --sup_smt_interval                      50000
% 3.56/1.00  
% 3.56/1.00  ------ Superposition Simplification Setup
% 3.56/1.00  
% 3.56/1.00  --sup_indices_passive                   []
% 3.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.00  --sup_full_bw                           [BwDemod]
% 3.56/1.00  --sup_immed_triv                        [TrivRules]
% 3.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.00  --sup_immed_bw_main                     []
% 3.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.00  
% 3.56/1.00  ------ Combination Options
% 3.56/1.00  
% 3.56/1.00  --comb_res_mult                         3
% 3.56/1.00  --comb_sup_mult                         2
% 3.56/1.00  --comb_inst_mult                        10
% 3.56/1.00  
% 3.56/1.00  ------ Debug Options
% 3.56/1.00  
% 3.56/1.00  --dbg_backtrace                         false
% 3.56/1.00  --dbg_dump_prop_clauses                 false
% 3.56/1.00  --dbg_dump_prop_clauses_file            -
% 3.56/1.00  --dbg_out_stat                          false
% 3.56/1.00  ------ Parsing...
% 3.56/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.00  ------ Proving...
% 3.56/1.00  ------ Problem Properties 
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  clauses                                 17
% 3.56/1.00  conjectures                             2
% 3.56/1.00  EPR                                     7
% 3.56/1.00  Horn                                    17
% 3.56/1.00  unary                                   7
% 3.56/1.00  binary                                  6
% 3.56/1.00  lits                                    31
% 3.56/1.00  lits eq                                 8
% 3.56/1.00  fd_pure                                 0
% 3.56/1.00  fd_pseudo                               0
% 3.56/1.00  fd_cond                                 1
% 3.56/1.00  fd_pseudo_cond                          1
% 3.56/1.00  AC symbols                              0
% 3.56/1.00  
% 3.56/1.00  ------ Input Options Time Limit: Unbounded
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ 
% 3.56/1.00  Current options:
% 3.56/1.00  ------ 
% 3.56/1.00  
% 3.56/1.00  ------ Input Options
% 3.56/1.00  
% 3.56/1.00  --out_options                           all
% 3.56/1.00  --tptp_safe_out                         true
% 3.56/1.00  --problem_path                          ""
% 3.56/1.00  --include_path                          ""
% 3.56/1.00  --clausifier                            res/vclausify_rel
% 3.56/1.00  --clausifier_options                    --mode clausify
% 3.56/1.00  --stdin                                 false
% 3.56/1.00  --stats_out                             sel
% 3.56/1.00  
% 3.56/1.00  ------ General Options
% 3.56/1.00  
% 3.56/1.00  --fof                                   false
% 3.56/1.00  --time_out_real                         604.99
% 3.56/1.00  --time_out_virtual                      -1.
% 3.56/1.00  --symbol_type_check                     false
% 3.56/1.00  --clausify_out                          false
% 3.56/1.00  --sig_cnt_out                           false
% 3.56/1.00  --trig_cnt_out                          false
% 3.56/1.00  --trig_cnt_out_tolerance                1.
% 3.56/1.00  --trig_cnt_out_sk_spl                   false
% 3.56/1.00  --abstr_cl_out                          false
% 3.56/1.00  
% 3.56/1.00  ------ Global Options
% 3.56/1.00  
% 3.56/1.00  --schedule                              none
% 3.56/1.00  --add_important_lit                     false
% 3.56/1.00  --prop_solver_per_cl                    1000
% 3.56/1.00  --min_unsat_core                        false
% 3.56/1.00  --soft_assumptions                      false
% 3.56/1.00  --soft_lemma_size                       3
% 3.56/1.00  --prop_impl_unit_size                   0
% 3.56/1.00  --prop_impl_unit                        []
% 3.56/1.00  --share_sel_clauses                     true
% 3.56/1.00  --reset_solvers                         false
% 3.56/1.00  --bc_imp_inh                            [conj_cone]
% 3.56/1.00  --conj_cone_tolerance                   3.
% 3.56/1.00  --extra_neg_conj                        none
% 3.56/1.00  --large_theory_mode                     true
% 3.56/1.00  --prolific_symb_bound                   200
% 3.56/1.00  --lt_threshold                          2000
% 3.56/1.00  --clause_weak_htbl                      true
% 3.56/1.00  --gc_record_bc_elim                     false
% 3.56/1.00  
% 3.56/1.00  ------ Preprocessing Options
% 3.56/1.00  
% 3.56/1.00  --preprocessing_flag                    true
% 3.56/1.00  --time_out_prep_mult                    0.1
% 3.56/1.00  --splitting_mode                        input
% 3.56/1.00  --splitting_grd                         true
% 3.56/1.00  --splitting_cvd                         false
% 3.56/1.00  --splitting_cvd_svl                     false
% 3.56/1.00  --splitting_nvd                         32
% 3.56/1.00  --sub_typing                            true
% 3.56/1.00  --prep_gs_sim                           false
% 3.56/1.00  --prep_unflatten                        true
% 3.56/1.00  --prep_res_sim                          true
% 3.56/1.00  --prep_upred                            true
% 3.56/1.00  --prep_sem_filter                       exhaustive
% 3.56/1.00  --prep_sem_filter_out                   false
% 3.56/1.00  --pred_elim                             false
% 3.56/1.00  --res_sim_input                         true
% 3.56/1.00  --eq_ax_congr_red                       true
% 3.56/1.00  --pure_diseq_elim                       true
% 3.56/1.00  --brand_transform                       false
% 3.56/1.00  --non_eq_to_eq                          false
% 3.56/1.00  --prep_def_merge                        true
% 3.56/1.00  --prep_def_merge_prop_impl              false
% 3.56/1.00  --prep_def_merge_mbd                    true
% 3.56/1.00  --prep_def_merge_tr_red                 false
% 3.56/1.00  --prep_def_merge_tr_cl                  false
% 3.56/1.00  --smt_preprocessing                     true
% 3.56/1.00  --smt_ac_axioms                         fast
% 3.56/1.00  --preprocessed_out                      false
% 3.56/1.00  --preprocessed_stats                    false
% 3.56/1.00  
% 3.56/1.00  ------ Abstraction refinement Options
% 3.56/1.00  
% 3.56/1.00  --abstr_ref                             []
% 3.56/1.00  --abstr_ref_prep                        false
% 3.56/1.00  --abstr_ref_until_sat                   false
% 3.56/1.00  --abstr_ref_sig_restrict                funpre
% 3.56/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/1.00  --abstr_ref_under                       []
% 3.56/1.00  
% 3.56/1.00  ------ SAT Options
% 3.56/1.00  
% 3.56/1.00  --sat_mode                              false
% 3.56/1.00  --sat_fm_restart_options                ""
% 3.56/1.00  --sat_gr_def                            false
% 3.56/1.00  --sat_epr_types                         true
% 3.56/1.00  --sat_non_cyclic_types                  false
% 3.56/1.00  --sat_finite_models                     false
% 3.56/1.00  --sat_fm_lemmas                         false
% 3.56/1.00  --sat_fm_prep                           false
% 3.56/1.00  --sat_fm_uc_incr                        true
% 3.56/1.00  --sat_out_model                         small
% 3.56/1.00  --sat_out_clauses                       false
% 3.56/1.00  
% 3.56/1.00  ------ QBF Options
% 3.56/1.00  
% 3.56/1.00  --qbf_mode                              false
% 3.56/1.00  --qbf_elim_univ                         false
% 3.56/1.00  --qbf_dom_inst                          none
% 3.56/1.00  --qbf_dom_pre_inst                      false
% 3.56/1.00  --qbf_sk_in                             false
% 3.56/1.00  --qbf_pred_elim                         true
% 3.56/1.00  --qbf_split                             512
% 3.56/1.00  
% 3.56/1.00  ------ BMC1 Options
% 3.56/1.00  
% 3.56/1.00  --bmc1_incremental                      false
% 3.56/1.00  --bmc1_axioms                           reachable_all
% 3.56/1.00  --bmc1_min_bound                        0
% 3.56/1.00  --bmc1_max_bound                        -1
% 3.56/1.00  --bmc1_max_bound_default                -1
% 3.56/1.00  --bmc1_symbol_reachability              true
% 3.56/1.00  --bmc1_property_lemmas                  false
% 3.56/1.00  --bmc1_k_induction                      false
% 3.56/1.00  --bmc1_non_equiv_states                 false
% 3.56/1.00  --bmc1_deadlock                         false
% 3.56/1.00  --bmc1_ucm                              false
% 3.56/1.00  --bmc1_add_unsat_core                   none
% 3.56/1.00  --bmc1_unsat_core_children              false
% 3.56/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/1.00  --bmc1_out_stat                         full
% 3.56/1.00  --bmc1_ground_init                      false
% 3.56/1.00  --bmc1_pre_inst_next_state              false
% 3.56/1.00  --bmc1_pre_inst_state                   false
% 3.56/1.00  --bmc1_pre_inst_reach_state             false
% 3.56/1.00  --bmc1_out_unsat_core                   false
% 3.56/1.00  --bmc1_aig_witness_out                  false
% 3.56/1.00  --bmc1_verbose                          false
% 3.56/1.00  --bmc1_dump_clauses_tptp                false
% 3.56/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.56/1.00  --bmc1_dump_file                        -
% 3.56/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.56/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.56/1.00  --bmc1_ucm_extend_mode                  1
% 3.56/1.00  --bmc1_ucm_init_mode                    2
% 3.56/1.00  --bmc1_ucm_cone_mode                    none
% 3.56/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.56/1.00  --bmc1_ucm_relax_model                  4
% 3.56/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.56/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/1.00  --bmc1_ucm_layered_model                none
% 3.56/1.00  --bmc1_ucm_max_lemma_size               10
% 3.56/1.00  
% 3.56/1.00  ------ AIG Options
% 3.56/1.00  
% 3.56/1.00  --aig_mode                              false
% 3.56/1.00  
% 3.56/1.00  ------ Instantiation Options
% 3.56/1.00  
% 3.56/1.00  --instantiation_flag                    true
% 3.56/1.00  --inst_sos_flag                         false
% 3.56/1.00  --inst_sos_phase                        true
% 3.56/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/1.00  --inst_lit_sel_side                     num_symb
% 3.56/1.00  --inst_solver_per_active                1400
% 3.56/1.00  --inst_solver_calls_frac                1.
% 3.56/1.00  --inst_passive_queue_type               priority_queues
% 3.56/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/1.00  --inst_passive_queues_freq              [25;2]
% 3.56/1.00  --inst_dismatching                      true
% 3.56/1.00  --inst_eager_unprocessed_to_passive     true
% 3.56/1.00  --inst_prop_sim_given                   true
% 3.56/1.00  --inst_prop_sim_new                     false
% 3.56/1.00  --inst_subs_new                         false
% 3.56/1.00  --inst_eq_res_simp                      false
% 3.56/1.00  --inst_subs_given                       false
% 3.56/1.00  --inst_orphan_elimination               true
% 3.56/1.00  --inst_learning_loop_flag               true
% 3.56/1.00  --inst_learning_start                   3000
% 3.56/1.00  --inst_learning_factor                  2
% 3.56/1.00  --inst_start_prop_sim_after_learn       3
% 3.56/1.00  --inst_sel_renew                        solver
% 3.56/1.00  --inst_lit_activity_flag                true
% 3.56/1.00  --inst_restr_to_given                   false
% 3.56/1.00  --inst_activity_threshold               500
% 3.56/1.00  --inst_out_proof                        true
% 3.56/1.00  
% 3.56/1.00  ------ Resolution Options
% 3.56/1.00  
% 3.56/1.00  --resolution_flag                       true
% 3.56/1.00  --res_lit_sel                           adaptive
% 3.56/1.00  --res_lit_sel_side                      none
% 3.56/1.00  --res_ordering                          kbo
% 3.56/1.00  --res_to_prop_solver                    active
% 3.56/1.00  --res_prop_simpl_new                    false
% 3.56/1.00  --res_prop_simpl_given                  true
% 3.56/1.00  --res_passive_queue_type                priority_queues
% 3.56/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/1.00  --res_passive_queues_freq               [15;5]
% 3.56/1.00  --res_forward_subs                      full
% 3.56/1.00  --res_backward_subs                     full
% 3.56/1.00  --res_forward_subs_resolution           true
% 3.56/1.00  --res_backward_subs_resolution          true
% 3.56/1.00  --res_orphan_elimination                true
% 3.56/1.00  --res_time_limit                        2.
% 3.56/1.00  --res_out_proof                         true
% 3.56/1.00  
% 3.56/1.00  ------ Superposition Options
% 3.56/1.00  
% 3.56/1.00  --superposition_flag                    true
% 3.56/1.00  --sup_passive_queue_type                priority_queues
% 3.56/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/1.00  --sup_passive_queues_freq               [1;4]
% 3.56/1.00  --demod_completeness_check              fast
% 3.56/1.00  --demod_use_ground                      true
% 3.56/1.00  --sup_to_prop_solver                    passive
% 3.56/1.00  --sup_prop_simpl_new                    true
% 3.56/1.00  --sup_prop_simpl_given                  true
% 3.56/1.00  --sup_fun_splitting                     false
% 3.56/1.00  --sup_smt_interval                      50000
% 3.56/1.00  
% 3.56/1.00  ------ Superposition Simplification Setup
% 3.56/1.00  
% 3.56/1.00  --sup_indices_passive                   []
% 3.56/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.00  --sup_full_bw                           [BwDemod]
% 3.56/1.00  --sup_immed_triv                        [TrivRules]
% 3.56/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.00  --sup_immed_bw_main                     []
% 3.56/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.00  
% 3.56/1.00  ------ Combination Options
% 3.56/1.00  
% 3.56/1.00  --comb_res_mult                         3
% 3.56/1.00  --comb_sup_mult                         2
% 3.56/1.00  --comb_inst_mult                        10
% 3.56/1.00  
% 3.56/1.00  ------ Debug Options
% 3.56/1.00  
% 3.56/1.00  --dbg_backtrace                         false
% 3.56/1.00  --dbg_dump_prop_clauses                 false
% 3.56/1.00  --dbg_dump_prop_clauses_file            -
% 3.56/1.00  --dbg_out_stat                          false
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  ------ Proving...
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  % SZS status Theorem for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  fof(f19,conjecture,(
% 3.56/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f20,negated_conjecture,(
% 3.56/1.00    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.56/1.00    inference(negated_conjecture,[],[f19])).
% 3.56/1.00  
% 3.56/1.00  fof(f30,plain,(
% 3.56/1.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f20])).
% 3.56/1.00  
% 3.56/1.00  fof(f33,plain,(
% 3.56/1.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 3.56/1.00    introduced(choice_axiom,[])).
% 3.56/1.00  
% 3.56/1.00  fof(f34,plain,(
% 3.56/1.00    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 3.56/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f33])).
% 3.56/1.00  
% 3.56/1.00  fof(f56,plain,(
% 3.56/1.00    v1_relat_1(sK0)),
% 3.56/1.00    inference(cnf_transformation,[],[f34])).
% 3.56/1.00  
% 3.56/1.00  fof(f1,axiom,(
% 3.56/1.00    v1_xboole_0(k1_xboole_0)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f35,plain,(
% 3.56/1.00    v1_xboole_0(k1_xboole_0)),
% 3.56/1.00    inference(cnf_transformation,[],[f1])).
% 3.56/1.00  
% 3.56/1.00  fof(f13,axiom,(
% 3.56/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f24,plain,(
% 3.56/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f13])).
% 3.56/1.00  
% 3.56/1.00  fof(f49,plain,(
% 3.56/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f24])).
% 3.56/1.00  
% 3.56/1.00  fof(f14,axiom,(
% 3.56/1.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f25,plain,(
% 3.56/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.56/1.00    inference(ennf_transformation,[],[f14])).
% 3.56/1.00  
% 3.56/1.00  fof(f26,plain,(
% 3.56/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.56/1.00    inference(flattening,[],[f25])).
% 3.56/1.00  
% 3.56/1.00  fof(f50,plain,(
% 3.56/1.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f26])).
% 3.56/1.00  
% 3.56/1.00  fof(f15,axiom,(
% 3.56/1.00    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f27,plain,(
% 3.56/1.00    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f15])).
% 3.56/1.00  
% 3.56/1.00  fof(f51,plain,(
% 3.56/1.00    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f27])).
% 3.56/1.00  
% 3.56/1.00  fof(f12,axiom,(
% 3.56/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f48,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.56/1.00    inference(cnf_transformation,[],[f12])).
% 3.56/1.00  
% 3.56/1.00  fof(f6,axiom,(
% 3.56/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f42,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f6])).
% 3.56/1.00  
% 3.56/1.00  fof(f7,axiom,(
% 3.56/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f43,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f7])).
% 3.56/1.00  
% 3.56/1.00  fof(f8,axiom,(
% 3.56/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f44,plain,(
% 3.56/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f8])).
% 3.56/1.00  
% 3.56/1.00  fof(f9,axiom,(
% 3.56/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f45,plain,(
% 3.56/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f9])).
% 3.56/1.00  
% 3.56/1.00  fof(f58,plain,(
% 3.56/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f44,f45])).
% 3.56/1.00  
% 3.56/1.00  fof(f59,plain,(
% 3.56/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f43,f58])).
% 3.56/1.00  
% 3.56/1.00  fof(f60,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f42,f59])).
% 3.56/1.00  
% 3.56/1.00  fof(f61,plain,(
% 3.56/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.56/1.00    inference(definition_unfolding,[],[f48,f60])).
% 3.56/1.00  
% 3.56/1.00  fof(f63,plain,(
% 3.56/1.00    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 3.56/1.00    inference(definition_unfolding,[],[f51,f61])).
% 3.56/1.00  
% 3.56/1.00  fof(f18,axiom,(
% 3.56/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f55,plain,(
% 3.56/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.56/1.00    inference(cnf_transformation,[],[f18])).
% 3.56/1.00  
% 3.56/1.00  fof(f17,axiom,(
% 3.56/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f29,plain,(
% 3.56/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f17])).
% 3.56/1.00  
% 3.56/1.00  fof(f53,plain,(
% 3.56/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f29])).
% 3.56/1.00  
% 3.56/1.00  fof(f5,axiom,(
% 3.56/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f41,plain,(
% 3.56/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f5])).
% 3.56/1.00  
% 3.56/1.00  fof(f3,axiom,(
% 3.56/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f31,plain,(
% 3.56/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/1.00    inference(nnf_transformation,[],[f3])).
% 3.56/1.00  
% 3.56/1.00  fof(f32,plain,(
% 3.56/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/1.00    inference(flattening,[],[f31])).
% 3.56/1.00  
% 3.56/1.00  fof(f39,plain,(
% 3.56/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f32])).
% 3.56/1.00  
% 3.56/1.00  fof(f4,axiom,(
% 3.56/1.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f40,plain,(
% 3.56/1.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f4])).
% 3.56/1.00  
% 3.56/1.00  fof(f62,plain,(
% 3.56/1.00    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 3.56/1.00    inference(definition_unfolding,[],[f40,f61])).
% 3.56/1.00  
% 3.56/1.00  fof(f10,axiom,(
% 3.56/1.00    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f22,plain,(
% 3.56/1.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.56/1.00    inference(ennf_transformation,[],[f10])).
% 3.56/1.00  
% 3.56/1.00  fof(f46,plain,(
% 3.56/1.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f22])).
% 3.56/1.00  
% 3.56/1.00  fof(f2,axiom,(
% 3.56/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f21,plain,(
% 3.56/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f2])).
% 3.56/1.00  
% 3.56/1.00  fof(f36,plain,(
% 3.56/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f21])).
% 3.56/1.00  
% 3.56/1.00  fof(f54,plain,(
% 3.56/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.56/1.00    inference(cnf_transformation,[],[f18])).
% 3.56/1.00  
% 3.56/1.00  fof(f16,axiom,(
% 3.56/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f28,plain,(
% 3.56/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f16])).
% 3.56/1.00  
% 3.56/1.00  fof(f52,plain,(
% 3.56/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f28])).
% 3.56/1.00  
% 3.56/1.00  fof(f11,axiom,(
% 3.56/1.00    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.56/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.00  
% 3.56/1.00  fof(f23,plain,(
% 3.56/1.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.56/1.00    inference(ennf_transformation,[],[f11])).
% 3.56/1.00  
% 3.56/1.00  fof(f47,plain,(
% 3.56/1.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.56/1.00    inference(cnf_transformation,[],[f23])).
% 3.56/1.00  
% 3.56/1.00  fof(f57,plain,(
% 3.56/1.00    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 3.56/1.00    inference(cnf_transformation,[],[f34])).
% 3.56/1.00  
% 3.56/1.00  cnf(c_17,negated_conjecture,
% 3.56/1.00      ( v1_relat_1(sK0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_442,plain,
% 3.56/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_0,plain,
% 3.56/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_454,plain,
% 3.56/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_9,plain,
% 3.56/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_447,plain,
% 3.56/1.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_910,plain,
% 3.56/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_454,c_447]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_10,plain,
% 3.56/1.00      ( ~ v1_relat_1(X0)
% 3.56/1.00      | ~ v1_relat_1(X1)
% 3.56/1.00      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.56/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_446,plain,
% 3.56/1.00      ( v1_relat_1(X0) != iProver_top
% 3.56/1.00      | v1_relat_1(X1) != iProver_top
% 3.56/1.00      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_11,plain,
% 3.56/1.00      ( ~ v1_relat_1(X0)
% 3.56/1.00      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_445,plain,
% 3.56/1.00      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1286,plain,
% 3.56/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 3.56/1.00      | v1_relat_1(X1) != iProver_top
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_446,c_445]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_2968,plain,
% 3.56/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_910,c_1286]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_7431,plain,
% 3.56/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_442,c_2968]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_14,plain,
% 3.56/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_13,plain,
% 3.56/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.56/1.00      | ~ v1_relat_1(X1)
% 3.56/1.00      | ~ v1_relat_1(X0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_443,plain,
% 3.56/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.56/1.00      | v1_relat_1(X1) != iProver_top
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_602,plain,
% 3.56/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 3.56/1.00      | v1_relat_1(X0) != iProver_top
% 3.56/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_14,c_443]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_31,plain,
% 3.56/1.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_33,plain,
% 3.56/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.56/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.56/1.00      inference(instantiation,[status(thm)],[c_31]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_50,plain,
% 3.56/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1291,plain,
% 3.56/1.00      ( v1_relat_1(X0) != iProver_top
% 3.56/1.00      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 3.56/1.00      inference(global_propositional_subsumption,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_602,c_33,c_50]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1292,plain,
% 3.56/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(renaming,[status(thm)],[c_1291]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6,plain,
% 3.56/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_450,plain,
% 3.56/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_2,plain,
% 3.56/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.56/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_452,plain,
% 3.56/1.00      ( X0 = X1
% 3.56/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.56/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1140,plain,
% 3.56/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_450,c_452]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1580,plain,
% 3.56/1.00      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_1292,c_1140]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_4755,plain,
% 3.56/1.00      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_442,c_1580]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_7446,plain,
% 3.56/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.56/1.00      inference(light_normalisation,[status(thm)],[c_7431,c_4755]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_5,plain,
% 3.56/1.00      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_7,plain,
% 3.56/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.56/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_449,plain,
% 3.56/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.56/1.00      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1,plain,
% 3.56/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_453,plain,
% 3.56/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1033,plain,
% 3.56/1.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.56/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_449,c_453]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1908,plain,
% 3.56/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_454,c_1033]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_7447,plain,
% 3.56/1.00      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.56/1.00      inference(demodulation,[status(thm)],[c_7446,c_5,c_1908]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_2967,plain,
% 3.56/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) = k5_relat_1(X0,sK0)
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_442,c_1286]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6653,plain,
% 3.56/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_910,c_2967]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_15,plain,
% 3.56/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.56/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_12,plain,
% 3.56/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 3.56/1.00      | ~ v1_relat_1(X1)
% 3.56/1.00      | ~ v1_relat_1(X0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_444,plain,
% 3.56/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 3.56/1.00      | v1_relat_1(X1) != iProver_top
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_903,plain,
% 3.56/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 3.56/1.00      | v1_relat_1(X0) != iProver_top
% 3.56/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_15,c_444]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1450,plain,
% 3.56/1.00      ( v1_relat_1(X0) != iProver_top
% 3.56/1.00      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 3.56/1.00      inference(global_propositional_subsumption,
% 3.56/1.00                [status(thm)],
% 3.56/1.00                [c_903,c_33,c_50]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1451,plain,
% 3.56/1.00      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(renaming,[status(thm)],[c_1450]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1581,plain,
% 3.56/1.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.56/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_1451,c_1140]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_5143,plain,
% 3.56/1.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_442,c_1581]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6665,plain,
% 3.56/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.56/1.00      inference(light_normalisation,[status(thm)],[c_6653,c_5143]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_8,plain,
% 3.56/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.56/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_448,plain,
% 3.56/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.56/1.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.56/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1014,plain,
% 3.56/1.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.56/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_448,c_453]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_1686,plain,
% 3.56/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.56/1.00      inference(superposition,[status(thm)],[c_454,c_1014]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6666,plain,
% 3.56/1.00      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 3.56/1.00      inference(demodulation,[status(thm)],[c_6665,c_5,c_1686]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_16,negated_conjecture,
% 3.56/1.00      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 3.56/1.00      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 3.56/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6838,plain,
% 3.56/1.00      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 3.56/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.56/1.00      inference(demodulation,[status(thm)],[c_6666,c_16]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(c_6839,plain,
% 3.56/1.00      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.56/1.00      inference(equality_resolution_simp,[status(thm)],[c_6838]) ).
% 3.56/1.00  
% 3.56/1.00  cnf(contradiction,plain,
% 3.56/1.00      ( $false ),
% 3.56/1.00      inference(minisat,[status(thm)],[c_7447,c_6839]) ).
% 3.56/1.00  
% 3.56/1.00  
% 3.56/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/1.00  
% 3.56/1.00  ------                               Statistics
% 3.56/1.00  
% 3.56/1.00  ------ Selected
% 3.56/1.00  
% 3.56/1.00  total_time:                             0.235
% 3.56/1.00  
%------------------------------------------------------------------------------
