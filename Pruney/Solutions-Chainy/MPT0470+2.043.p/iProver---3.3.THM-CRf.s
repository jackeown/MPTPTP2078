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
% DateTime   : Thu Dec  3 11:44:02 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 262 expanded)
%              Number of clauses        :   52 (  79 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   18
%              Number of atoms          :  241 ( 486 expanded)
%              Number of equality atoms :  157 ( 316 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f33])).

fof(f58,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f67,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f59,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_359,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_368,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_364,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_894,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_368,c_364])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_363,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_362,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1127,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_363,c_362])).

cnf(c_1887,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_1127])).

cnf(c_6992,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_359,c_1887])).

cnf(c_15,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_360,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_513,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_360])).

cnf(c_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_527,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_513,c_14])).

cnf(c_31,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_33,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_45,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1236,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_33,c_45])).

cnf(c_1237,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1236])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_365,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1243,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1237,c_365])).

cnf(c_1248,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_359,c_1243])).

cnf(c_6999,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6992,c_1248])).

cnf(c_4,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7000,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6999,c_4,c_6])).

cnf(c_1886,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) = k5_relat_1(X0,sK0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_1127])).

cnf(c_6262,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_894,c_1886])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_361,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_799,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_361])).

cnf(c_1132,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_799,c_33,c_45])).

cnf(c_1133,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1132])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_367,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1020,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_365,c_367])).

cnf(c_1477,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1133,c_1020])).

cnf(c_3737,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_359,c_1477])).

cnf(c_6264,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_6262,c_3737])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6265,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6264,c_4,c_7])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6386,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6265,c_16])).

cnf(c_6387,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6386])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7000,c_6387])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 4.09/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.07  
% 4.09/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.09/1.07  
% 4.09/1.07  ------  iProver source info
% 4.09/1.07  
% 4.09/1.07  git: date: 2020-06-30 10:37:57 +0100
% 4.09/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.09/1.07  git: non_committed_changes: false
% 4.09/1.07  git: last_make_outside_of_git: false
% 4.09/1.07  
% 4.09/1.07  ------ 
% 4.09/1.07  
% 4.09/1.07  ------ Input Options
% 4.09/1.07  
% 4.09/1.07  --out_options                           all
% 4.09/1.07  --tptp_safe_out                         true
% 4.09/1.07  --problem_path                          ""
% 4.09/1.07  --include_path                          ""
% 4.09/1.07  --clausifier                            res/vclausify_rel
% 4.09/1.07  --clausifier_options                    --mode clausify
% 4.09/1.07  --stdin                                 false
% 4.09/1.07  --stats_out                             sel
% 4.09/1.07  
% 4.09/1.07  ------ General Options
% 4.09/1.07  
% 4.09/1.07  --fof                                   false
% 4.09/1.07  --time_out_real                         604.97
% 4.09/1.07  --time_out_virtual                      -1.
% 4.09/1.07  --symbol_type_check                     false
% 4.09/1.07  --clausify_out                          false
% 4.09/1.07  --sig_cnt_out                           false
% 4.09/1.07  --trig_cnt_out                          false
% 4.09/1.07  --trig_cnt_out_tolerance                1.
% 4.09/1.07  --trig_cnt_out_sk_spl                   false
% 4.09/1.07  --abstr_cl_out                          false
% 4.09/1.07  
% 4.09/1.07  ------ Global Options
% 4.09/1.07  
% 4.09/1.07  --schedule                              none
% 4.09/1.07  --add_important_lit                     false
% 4.09/1.07  --prop_solver_per_cl                    1000
% 4.09/1.07  --min_unsat_core                        false
% 4.09/1.07  --soft_assumptions                      false
% 4.09/1.07  --soft_lemma_size                       3
% 4.09/1.07  --prop_impl_unit_size                   0
% 4.09/1.07  --prop_impl_unit                        []
% 4.09/1.07  --share_sel_clauses                     true
% 4.09/1.07  --reset_solvers                         false
% 4.09/1.07  --bc_imp_inh                            [conj_cone]
% 4.09/1.07  --conj_cone_tolerance                   3.
% 4.09/1.07  --extra_neg_conj                        none
% 4.09/1.07  --large_theory_mode                     true
% 4.09/1.07  --prolific_symb_bound                   200
% 4.09/1.07  --lt_threshold                          2000
% 4.09/1.07  --clause_weak_htbl                      true
% 4.09/1.07  --gc_record_bc_elim                     false
% 4.09/1.07  
% 4.09/1.07  ------ Preprocessing Options
% 4.09/1.07  
% 4.09/1.07  --preprocessing_flag                    true
% 4.09/1.07  --time_out_prep_mult                    0.1
% 4.09/1.07  --splitting_mode                        input
% 4.09/1.07  --splitting_grd                         true
% 4.09/1.07  --splitting_cvd                         false
% 4.09/1.07  --splitting_cvd_svl                     false
% 4.09/1.07  --splitting_nvd                         32
% 4.09/1.07  --sub_typing                            true
% 4.09/1.07  --prep_gs_sim                           false
% 4.09/1.07  --prep_unflatten                        true
% 4.09/1.07  --prep_res_sim                          true
% 4.09/1.07  --prep_upred                            true
% 4.09/1.07  --prep_sem_filter                       exhaustive
% 4.09/1.07  --prep_sem_filter_out                   false
% 4.09/1.07  --pred_elim                             false
% 4.09/1.07  --res_sim_input                         true
% 4.09/1.07  --eq_ax_congr_red                       true
% 4.09/1.07  --pure_diseq_elim                       true
% 4.09/1.07  --brand_transform                       false
% 4.09/1.07  --non_eq_to_eq                          false
% 4.09/1.07  --prep_def_merge                        true
% 4.09/1.07  --prep_def_merge_prop_impl              false
% 4.09/1.07  --prep_def_merge_mbd                    true
% 4.09/1.07  --prep_def_merge_tr_red                 false
% 4.09/1.07  --prep_def_merge_tr_cl                  false
% 4.09/1.07  --smt_preprocessing                     true
% 4.09/1.07  --smt_ac_axioms                         fast
% 4.09/1.07  --preprocessed_out                      false
% 4.09/1.07  --preprocessed_stats                    false
% 4.09/1.07  
% 4.09/1.07  ------ Abstraction refinement Options
% 4.09/1.07  
% 4.09/1.07  --abstr_ref                             []
% 4.09/1.07  --abstr_ref_prep                        false
% 4.09/1.07  --abstr_ref_until_sat                   false
% 4.09/1.07  --abstr_ref_sig_restrict                funpre
% 4.09/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 4.09/1.07  --abstr_ref_under                       []
% 4.09/1.07  
% 4.09/1.07  ------ SAT Options
% 4.09/1.07  
% 4.09/1.07  --sat_mode                              false
% 4.09/1.07  --sat_fm_restart_options                ""
% 4.09/1.07  --sat_gr_def                            false
% 4.09/1.07  --sat_epr_types                         true
% 4.09/1.07  --sat_non_cyclic_types                  false
% 4.09/1.07  --sat_finite_models                     false
% 4.09/1.07  --sat_fm_lemmas                         false
% 4.09/1.07  --sat_fm_prep                           false
% 4.09/1.07  --sat_fm_uc_incr                        true
% 4.09/1.07  --sat_out_model                         small
% 4.09/1.07  --sat_out_clauses                       false
% 4.09/1.07  
% 4.09/1.07  ------ QBF Options
% 4.09/1.07  
% 4.09/1.07  --qbf_mode                              false
% 4.09/1.07  --qbf_elim_univ                         false
% 4.09/1.07  --qbf_dom_inst                          none
% 4.09/1.07  --qbf_dom_pre_inst                      false
% 4.09/1.07  --qbf_sk_in                             false
% 4.09/1.07  --qbf_pred_elim                         true
% 4.09/1.07  --qbf_split                             512
% 4.09/1.07  
% 4.09/1.07  ------ BMC1 Options
% 4.09/1.07  
% 4.09/1.07  --bmc1_incremental                      false
% 4.09/1.07  --bmc1_axioms                           reachable_all
% 4.09/1.07  --bmc1_min_bound                        0
% 4.09/1.07  --bmc1_max_bound                        -1
% 4.09/1.07  --bmc1_max_bound_default                -1
% 4.09/1.07  --bmc1_symbol_reachability              true
% 4.09/1.07  --bmc1_property_lemmas                  false
% 4.09/1.07  --bmc1_k_induction                      false
% 4.09/1.07  --bmc1_non_equiv_states                 false
% 4.09/1.07  --bmc1_deadlock                         false
% 4.09/1.07  --bmc1_ucm                              false
% 4.09/1.07  --bmc1_add_unsat_core                   none
% 4.09/1.07  --bmc1_unsat_core_children              false
% 4.09/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 4.09/1.07  --bmc1_out_stat                         full
% 4.09/1.07  --bmc1_ground_init                      false
% 4.09/1.07  --bmc1_pre_inst_next_state              false
% 4.09/1.07  --bmc1_pre_inst_state                   false
% 4.09/1.07  --bmc1_pre_inst_reach_state             false
% 4.09/1.07  --bmc1_out_unsat_core                   false
% 4.09/1.07  --bmc1_aig_witness_out                  false
% 4.09/1.07  --bmc1_verbose                          false
% 4.09/1.07  --bmc1_dump_clauses_tptp                false
% 4.09/1.07  --bmc1_dump_unsat_core_tptp             false
% 4.09/1.07  --bmc1_dump_file                        -
% 4.09/1.07  --bmc1_ucm_expand_uc_limit              128
% 4.09/1.07  --bmc1_ucm_n_expand_iterations          6
% 4.09/1.07  --bmc1_ucm_extend_mode                  1
% 4.09/1.07  --bmc1_ucm_init_mode                    2
% 4.09/1.07  --bmc1_ucm_cone_mode                    none
% 4.09/1.07  --bmc1_ucm_reduced_relation_type        0
% 4.09/1.07  --bmc1_ucm_relax_model                  4
% 4.09/1.07  --bmc1_ucm_full_tr_after_sat            true
% 4.09/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 4.09/1.07  --bmc1_ucm_layered_model                none
% 4.09/1.07  --bmc1_ucm_max_lemma_size               10
% 4.09/1.07  
% 4.09/1.07  ------ AIG Options
% 4.09/1.07  
% 4.09/1.07  --aig_mode                              false
% 4.09/1.07  
% 4.09/1.07  ------ Instantiation Options
% 4.09/1.07  
% 4.09/1.07  --instantiation_flag                    true
% 4.09/1.07  --inst_sos_flag                         false
% 4.09/1.07  --inst_sos_phase                        true
% 4.09/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.09/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.09/1.07  --inst_lit_sel_side                     num_symb
% 4.09/1.07  --inst_solver_per_active                1400
% 4.09/1.07  --inst_solver_calls_frac                1.
% 4.09/1.07  --inst_passive_queue_type               priority_queues
% 4.09/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.09/1.07  --inst_passive_queues_freq              [25;2]
% 4.09/1.07  --inst_dismatching                      true
% 4.09/1.07  --inst_eager_unprocessed_to_passive     true
% 4.09/1.07  --inst_prop_sim_given                   true
% 4.09/1.07  --inst_prop_sim_new                     false
% 4.09/1.07  --inst_subs_new                         false
% 4.09/1.07  --inst_eq_res_simp                      false
% 4.09/1.07  --inst_subs_given                       false
% 4.09/1.07  --inst_orphan_elimination               true
% 4.09/1.07  --inst_learning_loop_flag               true
% 4.09/1.07  --inst_learning_start                   3000
% 4.09/1.07  --inst_learning_factor                  2
% 4.09/1.07  --inst_start_prop_sim_after_learn       3
% 4.09/1.07  --inst_sel_renew                        solver
% 4.09/1.07  --inst_lit_activity_flag                true
% 4.09/1.07  --inst_restr_to_given                   false
% 4.09/1.07  --inst_activity_threshold               500
% 4.09/1.07  --inst_out_proof                        true
% 4.09/1.07  
% 4.09/1.07  ------ Resolution Options
% 4.09/1.07  
% 4.09/1.07  --resolution_flag                       true
% 4.09/1.07  --res_lit_sel                           adaptive
% 4.09/1.07  --res_lit_sel_side                      none
% 4.09/1.07  --res_ordering                          kbo
% 4.09/1.07  --res_to_prop_solver                    active
% 4.09/1.07  --res_prop_simpl_new                    false
% 4.09/1.07  --res_prop_simpl_given                  true
% 4.09/1.07  --res_passive_queue_type                priority_queues
% 4.09/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.09/1.07  --res_passive_queues_freq               [15;5]
% 4.09/1.07  --res_forward_subs                      full
% 4.09/1.07  --res_backward_subs                     full
% 4.09/1.07  --res_forward_subs_resolution           true
% 4.09/1.07  --res_backward_subs_resolution          true
% 4.09/1.07  --res_orphan_elimination                true
% 4.09/1.07  --res_time_limit                        2.
% 4.09/1.07  --res_out_proof                         true
% 4.09/1.07  
% 4.09/1.07  ------ Superposition Options
% 4.09/1.07  
% 4.09/1.07  --superposition_flag                    true
% 4.09/1.07  --sup_passive_queue_type                priority_queues
% 4.09/1.07  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.09/1.07  --sup_passive_queues_freq               [1;4]
% 4.09/1.07  --demod_completeness_check              fast
% 4.09/1.07  --demod_use_ground                      true
% 4.09/1.07  --sup_to_prop_solver                    passive
% 4.09/1.07  --sup_prop_simpl_new                    true
% 4.09/1.07  --sup_prop_simpl_given                  true
% 4.09/1.07  --sup_fun_splitting                     false
% 4.09/1.07  --sup_smt_interval                      50000
% 4.09/1.07  
% 4.09/1.07  ------ Superposition Simplification Setup
% 4.09/1.07  
% 4.09/1.07  --sup_indices_passive                   []
% 4.09/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.09/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.09/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.09/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 4.09/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.09/1.07  --sup_full_bw                           [BwDemod]
% 4.09/1.07  --sup_immed_triv                        [TrivRules]
% 4.09/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.09/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.09/1.07  --sup_immed_bw_main                     []
% 4.09/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.09/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 4.09/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.09/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.09/1.07  
% 4.09/1.07  ------ Combination Options
% 4.09/1.07  
% 4.09/1.07  --comb_res_mult                         3
% 4.09/1.07  --comb_sup_mult                         2
% 4.09/1.07  --comb_inst_mult                        10
% 4.09/1.07  
% 4.09/1.07  ------ Debug Options
% 4.09/1.07  
% 4.09/1.07  --dbg_backtrace                         false
% 4.09/1.07  --dbg_dump_prop_clauses                 false
% 4.09/1.07  --dbg_dump_prop_clauses_file            -
% 4.09/1.07  --dbg_out_stat                          false
% 4.09/1.07  ------ Parsing...
% 4.09/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.09/1.07  
% 4.09/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.09/1.07  
% 4.09/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.09/1.07  
% 4.09/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.09/1.07  ------ Proving...
% 4.09/1.07  ------ Problem Properties 
% 4.09/1.07  
% 4.09/1.07  
% 4.09/1.07  clauses                                 17
% 4.09/1.07  conjectures                             2
% 4.09/1.07  EPR                                     6
% 4.09/1.07  Horn                                    16
% 4.09/1.07  unary                                   9
% 4.09/1.07  binary                                  3
% 4.09/1.07  lits                                    31
% 4.09/1.07  lits eq                                 13
% 4.09/1.07  fd_pure                                 0
% 4.09/1.07  fd_pseudo                               0
% 4.09/1.07  fd_cond                                 1
% 4.09/1.07  fd_pseudo_cond                          1
% 4.09/1.07  AC symbols                              0
% 4.09/1.07  
% 4.09/1.07  ------ Input Options Time Limit: Unbounded
% 4.09/1.07  
% 4.09/1.07  
% 4.09/1.07  ------ 
% 4.09/1.07  Current options:
% 4.09/1.07  ------ 
% 4.09/1.07  
% 4.09/1.07  ------ Input Options
% 4.09/1.07  
% 4.09/1.07  --out_options                           all
% 4.09/1.07  --tptp_safe_out                         true
% 4.09/1.07  --problem_path                          ""
% 4.09/1.07  --include_path                          ""
% 4.09/1.07  --clausifier                            res/vclausify_rel
% 4.09/1.07  --clausifier_options                    --mode clausify
% 4.09/1.07  --stdin                                 false
% 4.09/1.07  --stats_out                             sel
% 4.09/1.07  
% 4.09/1.07  ------ General Options
% 4.09/1.07  
% 4.09/1.07  --fof                                   false
% 4.09/1.07  --time_out_real                         604.97
% 4.09/1.07  --time_out_virtual                      -1.
% 4.09/1.07  --symbol_type_check                     false
% 4.09/1.07  --clausify_out                          false
% 4.09/1.07  --sig_cnt_out                           false
% 4.09/1.07  --trig_cnt_out                          false
% 4.09/1.07  --trig_cnt_out_tolerance                1.
% 4.09/1.07  --trig_cnt_out_sk_spl                   false
% 4.09/1.07  --abstr_cl_out                          false
% 4.09/1.07  
% 4.09/1.07  ------ Global Options
% 4.09/1.07  
% 4.09/1.07  --schedule                              none
% 4.09/1.07  --add_important_lit                     false
% 4.09/1.07  --prop_solver_per_cl                    1000
% 4.09/1.07  --min_unsat_core                        false
% 4.09/1.07  --soft_assumptions                      false
% 4.09/1.07  --soft_lemma_size                       3
% 4.09/1.07  --prop_impl_unit_size                   0
% 4.09/1.07  --prop_impl_unit                        []
% 4.09/1.07  --share_sel_clauses                     true
% 4.09/1.07  --reset_solvers                         false
% 4.09/1.07  --bc_imp_inh                            [conj_cone]
% 4.09/1.07  --conj_cone_tolerance                   3.
% 4.09/1.07  --extra_neg_conj                        none
% 4.09/1.07  --large_theory_mode                     true
% 4.09/1.07  --prolific_symb_bound                   200
% 4.09/1.07  --lt_threshold                          2000
% 4.09/1.07  --clause_weak_htbl                      true
% 4.09/1.07  --gc_record_bc_elim                     false
% 4.09/1.07  
% 4.09/1.07  ------ Preprocessing Options
% 4.09/1.07  
% 4.09/1.07  --preprocessing_flag                    true
% 4.09/1.07  --time_out_prep_mult                    0.1
% 4.09/1.07  --splitting_mode                        input
% 4.09/1.07  --splitting_grd                         true
% 4.09/1.07  --splitting_cvd                         false
% 4.09/1.07  --splitting_cvd_svl                     false
% 4.09/1.07  --splitting_nvd                         32
% 4.09/1.07  --sub_typing                            true
% 4.09/1.07  --prep_gs_sim                           false
% 4.09/1.07  --prep_unflatten                        true
% 4.09/1.07  --prep_res_sim                          true
% 4.09/1.07  --prep_upred                            true
% 4.09/1.07  --prep_sem_filter                       exhaustive
% 4.09/1.07  --prep_sem_filter_out                   false
% 4.09/1.07  --pred_elim                             false
% 4.09/1.07  --res_sim_input                         true
% 4.09/1.07  --eq_ax_congr_red                       true
% 4.09/1.07  --pure_diseq_elim                       true
% 4.09/1.07  --brand_transform                       false
% 4.09/1.07  --non_eq_to_eq                          false
% 4.09/1.07  --prep_def_merge                        true
% 4.09/1.07  --prep_def_merge_prop_impl              false
% 4.09/1.07  --prep_def_merge_mbd                    true
% 4.09/1.07  --prep_def_merge_tr_red                 false
% 4.09/1.07  --prep_def_merge_tr_cl                  false
% 4.09/1.07  --smt_preprocessing                     true
% 4.09/1.07  --smt_ac_axioms                         fast
% 4.09/1.07  --preprocessed_out                      false
% 4.09/1.07  --preprocessed_stats                    false
% 4.09/1.07  
% 4.09/1.07  ------ Abstraction refinement Options
% 4.09/1.07  
% 4.09/1.07  --abstr_ref                             []
% 4.09/1.07  --abstr_ref_prep                        false
% 4.09/1.07  --abstr_ref_until_sat                   false
% 4.09/1.07  --abstr_ref_sig_restrict                funpre
% 4.09/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 4.09/1.07  --abstr_ref_under                       []
% 4.09/1.07  
% 4.09/1.07  ------ SAT Options
% 4.09/1.07  
% 4.09/1.07  --sat_mode                              false
% 4.09/1.07  --sat_fm_restart_options                ""
% 4.09/1.07  --sat_gr_def                            false
% 4.09/1.07  --sat_epr_types                         true
% 4.09/1.07  --sat_non_cyclic_types                  false
% 4.09/1.07  --sat_finite_models                     false
% 4.09/1.07  --sat_fm_lemmas                         false
% 4.09/1.07  --sat_fm_prep                           false
% 4.09/1.07  --sat_fm_uc_incr                        true
% 4.09/1.07  --sat_out_model                         small
% 4.09/1.07  --sat_out_clauses                       false
% 4.09/1.07  
% 4.09/1.07  ------ QBF Options
% 4.09/1.07  
% 4.09/1.07  --qbf_mode                              false
% 4.09/1.07  --qbf_elim_univ                         false
% 4.09/1.07  --qbf_dom_inst                          none
% 4.09/1.07  --qbf_dom_pre_inst                      false
% 4.09/1.07  --qbf_sk_in                             false
% 4.09/1.07  --qbf_pred_elim                         true
% 4.09/1.07  --qbf_split                             512
% 4.09/1.07  
% 4.09/1.07  ------ BMC1 Options
% 4.09/1.07  
% 4.09/1.07  --bmc1_incremental                      false
% 4.09/1.07  --bmc1_axioms                           reachable_all
% 4.09/1.07  --bmc1_min_bound                        0
% 4.09/1.07  --bmc1_max_bound                        -1
% 4.09/1.07  --bmc1_max_bound_default                -1
% 4.09/1.07  --bmc1_symbol_reachability              true
% 4.09/1.07  --bmc1_property_lemmas                  false
% 4.09/1.07  --bmc1_k_induction                      false
% 4.09/1.07  --bmc1_non_equiv_states                 false
% 4.09/1.07  --bmc1_deadlock                         false
% 4.09/1.07  --bmc1_ucm                              false
% 4.09/1.07  --bmc1_add_unsat_core                   none
% 4.09/1.07  --bmc1_unsat_core_children              false
% 4.09/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 4.09/1.07  --bmc1_out_stat                         full
% 4.09/1.07  --bmc1_ground_init                      false
% 4.09/1.07  --bmc1_pre_inst_next_state              false
% 4.09/1.07  --bmc1_pre_inst_state                   false
% 4.09/1.07  --bmc1_pre_inst_reach_state             false
% 4.09/1.07  --bmc1_out_unsat_core                   false
% 4.09/1.07  --bmc1_aig_witness_out                  false
% 4.09/1.07  --bmc1_verbose                          false
% 4.09/1.07  --bmc1_dump_clauses_tptp                false
% 4.09/1.07  --bmc1_dump_unsat_core_tptp             false
% 4.09/1.07  --bmc1_dump_file                        -
% 4.09/1.07  --bmc1_ucm_expand_uc_limit              128
% 4.09/1.07  --bmc1_ucm_n_expand_iterations          6
% 4.09/1.07  --bmc1_ucm_extend_mode                  1
% 4.09/1.07  --bmc1_ucm_init_mode                    2
% 4.09/1.07  --bmc1_ucm_cone_mode                    none
% 4.09/1.07  --bmc1_ucm_reduced_relation_type        0
% 4.09/1.07  --bmc1_ucm_relax_model                  4
% 4.09/1.07  --bmc1_ucm_full_tr_after_sat            true
% 4.09/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 4.09/1.07  --bmc1_ucm_layered_model                none
% 4.09/1.07  --bmc1_ucm_max_lemma_size               10
% 4.09/1.07  
% 4.09/1.07  ------ AIG Options
% 4.09/1.07  
% 4.09/1.07  --aig_mode                              false
% 4.09/1.07  
% 4.09/1.07  ------ Instantiation Options
% 4.09/1.07  
% 4.09/1.07  --instantiation_flag                    true
% 4.09/1.07  --inst_sos_flag                         false
% 4.09/1.07  --inst_sos_phase                        true
% 4.09/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.09/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.09/1.07  --inst_lit_sel_side                     num_symb
% 4.09/1.07  --inst_solver_per_active                1400
% 4.09/1.07  --inst_solver_calls_frac                1.
% 4.09/1.07  --inst_passive_queue_type               priority_queues
% 4.09/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.09/1.07  --inst_passive_queues_freq              [25;2]
% 4.09/1.07  --inst_dismatching                      true
% 4.09/1.07  --inst_eager_unprocessed_to_passive     true
% 4.09/1.07  --inst_prop_sim_given                   true
% 4.09/1.07  --inst_prop_sim_new                     false
% 4.09/1.07  --inst_subs_new                         false
% 4.09/1.07  --inst_eq_res_simp                      false
% 4.09/1.07  --inst_subs_given                       false
% 4.09/1.07  --inst_orphan_elimination               true
% 4.09/1.07  --inst_learning_loop_flag               true
% 4.09/1.07  --inst_learning_start                   3000
% 4.09/1.07  --inst_learning_factor                  2
% 4.09/1.07  --inst_start_prop_sim_after_learn       3
% 4.09/1.07  --inst_sel_renew                        solver
% 4.09/1.07  --inst_lit_activity_flag                true
% 4.09/1.07  --inst_restr_to_given                   false
% 4.09/1.07  --inst_activity_threshold               500
% 4.09/1.07  --inst_out_proof                        true
% 4.09/1.07  
% 4.09/1.07  ------ Resolution Options
% 4.09/1.07  
% 4.09/1.07  --resolution_flag                       true
% 4.09/1.07  --res_lit_sel                           adaptive
% 4.09/1.07  --res_lit_sel_side                      none
% 4.09/1.07  --res_ordering                          kbo
% 4.09/1.07  --res_to_prop_solver                    active
% 4.09/1.07  --res_prop_simpl_new                    false
% 4.09/1.07  --res_prop_simpl_given                  true
% 4.09/1.07  --res_passive_queue_type                priority_queues
% 4.09/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.09/1.07  --res_passive_queues_freq               [15;5]
% 4.09/1.07  --res_forward_subs                      full
% 4.09/1.07  --res_backward_subs                     full
% 4.09/1.07  --res_forward_subs_resolution           true
% 4.09/1.07  --res_backward_subs_resolution          true
% 4.09/1.07  --res_orphan_elimination                true
% 4.09/1.07  --res_time_limit                        2.
% 4.09/1.07  --res_out_proof                         true
% 4.09/1.07  
% 4.09/1.07  ------ Superposition Options
% 4.09/1.07  
% 4.09/1.07  --superposition_flag                    true
% 4.09/1.07  --sup_passive_queue_type                priority_queues
% 4.09/1.07  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.09/1.07  --sup_passive_queues_freq               [1;4]
% 4.09/1.07  --demod_completeness_check              fast
% 4.09/1.07  --demod_use_ground                      true
% 4.09/1.07  --sup_to_prop_solver                    passive
% 4.09/1.07  --sup_prop_simpl_new                    true
% 4.09/1.07  --sup_prop_simpl_given                  true
% 4.09/1.07  --sup_fun_splitting                     false
% 4.09/1.07  --sup_smt_interval                      50000
% 4.09/1.07  
% 4.09/1.07  ------ Superposition Simplification Setup
% 4.09/1.07  
% 4.09/1.07  --sup_indices_passive                   []
% 4.09/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.09/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.09/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.09/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 4.09/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.09/1.07  --sup_full_bw                           [BwDemod]
% 4.09/1.07  --sup_immed_triv                        [TrivRules]
% 4.09/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.09/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.09/1.07  --sup_immed_bw_main                     []
% 4.09/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.09/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 4.09/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.09/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.09/1.07  
% 4.09/1.07  ------ Combination Options
% 4.09/1.07  
% 4.09/1.07  --comb_res_mult                         3
% 4.09/1.07  --comb_sup_mult                         2
% 4.09/1.07  --comb_inst_mult                        10
% 4.09/1.07  
% 4.09/1.07  ------ Debug Options
% 4.09/1.07  
% 4.09/1.07  --dbg_backtrace                         false
% 4.09/1.07  --dbg_dump_prop_clauses                 false
% 4.09/1.07  --dbg_dump_prop_clauses_file            -
% 4.09/1.07  --dbg_out_stat                          false
% 4.09/1.07  
% 4.09/1.07  
% 4.09/1.07  
% 4.09/1.07  
% 4.09/1.07  ------ Proving...
% 4.09/1.07  
% 4.09/1.07  
% 4.09/1.07  % SZS status Theorem for theBenchmark.p
% 4.09/1.07  
% 4.09/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 4.09/1.07  
% 4.09/1.07  fof(f19,conjecture,(
% 4.09/1.07    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f20,negated_conjecture,(
% 4.09/1.07    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 4.09/1.07    inference(negated_conjecture,[],[f19])).
% 4.09/1.07  
% 4.09/1.07  fof(f28,plain,(
% 4.09/1.07    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 4.09/1.07    inference(ennf_transformation,[],[f20])).
% 4.09/1.07  
% 4.09/1.07  fof(f33,plain,(
% 4.09/1.07    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 4.09/1.07    introduced(choice_axiom,[])).
% 4.09/1.07  
% 4.09/1.07  fof(f34,plain,(
% 4.09/1.07    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 4.09/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f33])).
% 4.09/1.07  
% 4.09/1.07  fof(f58,plain,(
% 4.09/1.07    v1_relat_1(sK0)),
% 4.09/1.07    inference(cnf_transformation,[],[f34])).
% 4.09/1.07  
% 4.09/1.07  fof(f1,axiom,(
% 4.09/1.07    v1_xboole_0(k1_xboole_0)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f35,plain,(
% 4.09/1.07    v1_xboole_0(k1_xboole_0)),
% 4.09/1.07    inference(cnf_transformation,[],[f1])).
% 4.09/1.07  
% 4.09/1.07  fof(f13,axiom,(
% 4.09/1.07    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f21,plain,(
% 4.09/1.07    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 4.09/1.07    inference(ennf_transformation,[],[f13])).
% 4.09/1.07  
% 4.09/1.07  fof(f51,plain,(
% 4.09/1.07    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f21])).
% 4.09/1.07  
% 4.09/1.07  fof(f14,axiom,(
% 4.09/1.07    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f22,plain,(
% 4.09/1.07    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 4.09/1.07    inference(ennf_transformation,[],[f14])).
% 4.09/1.07  
% 4.09/1.07  fof(f23,plain,(
% 4.09/1.07    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 4.09/1.07    inference(flattening,[],[f22])).
% 4.09/1.07  
% 4.09/1.07  fof(f52,plain,(
% 4.09/1.07    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f23])).
% 4.09/1.07  
% 4.09/1.07  fof(f15,axiom,(
% 4.09/1.07    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f24,plain,(
% 4.09/1.07    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 4.09/1.07    inference(ennf_transformation,[],[f15])).
% 4.09/1.07  
% 4.09/1.07  fof(f53,plain,(
% 4.09/1.07    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f24])).
% 4.09/1.07  
% 4.09/1.07  fof(f12,axiom,(
% 4.09/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f50,plain,(
% 4.09/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.09/1.07    inference(cnf_transformation,[],[f12])).
% 4.09/1.07  
% 4.09/1.07  fof(f5,axiom,(
% 4.09/1.07    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f41,plain,(
% 4.09/1.07    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f5])).
% 4.09/1.07  
% 4.09/1.07  fof(f6,axiom,(
% 4.09/1.07    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f42,plain,(
% 4.09/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f6])).
% 4.09/1.07  
% 4.09/1.07  fof(f7,axiom,(
% 4.09/1.07    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f43,plain,(
% 4.09/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f7])).
% 4.09/1.07  
% 4.09/1.07  fof(f8,axiom,(
% 4.09/1.07    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f44,plain,(
% 4.09/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f8])).
% 4.09/1.07  
% 4.09/1.07  fof(f9,axiom,(
% 4.09/1.07    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f45,plain,(
% 4.09/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f9])).
% 4.09/1.07  
% 4.09/1.07  fof(f10,axiom,(
% 4.09/1.07    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f46,plain,(
% 4.09/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f10])).
% 4.09/1.07  
% 4.09/1.07  fof(f60,plain,(
% 4.09/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.09/1.07    inference(definition_unfolding,[],[f45,f46])).
% 4.09/1.07  
% 4.09/1.07  fof(f61,plain,(
% 4.09/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.09/1.07    inference(definition_unfolding,[],[f44,f60])).
% 4.09/1.07  
% 4.09/1.07  fof(f62,plain,(
% 4.09/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.09/1.07    inference(definition_unfolding,[],[f43,f61])).
% 4.09/1.07  
% 4.09/1.07  fof(f63,plain,(
% 4.09/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.09/1.07    inference(definition_unfolding,[],[f42,f62])).
% 4.09/1.07  
% 4.09/1.07  fof(f64,plain,(
% 4.09/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.09/1.07    inference(definition_unfolding,[],[f41,f63])).
% 4.09/1.07  
% 4.09/1.07  fof(f65,plain,(
% 4.09/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.09/1.07    inference(definition_unfolding,[],[f50,f64])).
% 4.09/1.07  
% 4.09/1.07  fof(f67,plain,(
% 4.09/1.07    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 4.09/1.07    inference(definition_unfolding,[],[f53,f65])).
% 4.09/1.07  
% 4.09/1.07  fof(f18,axiom,(
% 4.09/1.07    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f56,plain,(
% 4.09/1.07    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.09/1.07    inference(cnf_transformation,[],[f18])).
% 4.09/1.07  
% 4.09/1.07  fof(f17,axiom,(
% 4.09/1.07    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f26,plain,(
% 4.09/1.07    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.09/1.07    inference(ennf_transformation,[],[f17])).
% 4.09/1.07  
% 4.09/1.07  fof(f27,plain,(
% 4.09/1.07    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.09/1.07    inference(flattening,[],[f26])).
% 4.09/1.07  
% 4.09/1.07  fof(f55,plain,(
% 4.09/1.07    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f27])).
% 4.09/1.07  
% 4.09/1.07  fof(f57,plain,(
% 4.09/1.07    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 4.09/1.07    inference(cnf_transformation,[],[f18])).
% 4.09/1.07  
% 4.09/1.07  fof(f4,axiom,(
% 4.09/1.07    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f40,plain,(
% 4.09/1.07    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f4])).
% 4.09/1.07  
% 4.09/1.07  fof(f3,axiom,(
% 4.09/1.07    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f39,plain,(
% 4.09/1.07    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 4.09/1.07    inference(cnf_transformation,[],[f3])).
% 4.09/1.07  
% 4.09/1.07  fof(f66,plain,(
% 4.09/1.07    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 4.09/1.07    inference(definition_unfolding,[],[f39,f65])).
% 4.09/1.07  
% 4.09/1.07  fof(f11,axiom,(
% 4.09/1.07    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f31,plain,(
% 4.09/1.07    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.09/1.07    inference(nnf_transformation,[],[f11])).
% 4.09/1.07  
% 4.09/1.07  fof(f32,plain,(
% 4.09/1.07    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.09/1.07    inference(flattening,[],[f31])).
% 4.09/1.07  
% 4.09/1.07  fof(f49,plain,(
% 4.09/1.07    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.09/1.07    inference(cnf_transformation,[],[f32])).
% 4.09/1.07  
% 4.09/1.07  fof(f70,plain,(
% 4.09/1.07    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.09/1.07    inference(equality_resolution,[],[f49])).
% 4.09/1.07  
% 4.09/1.07  fof(f16,axiom,(
% 4.09/1.07    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 4.09/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.07  
% 4.09/1.07  fof(f25,plain,(
% 4.09/1.07    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.09/1.07    inference(ennf_transformation,[],[f16])).
% 4.09/1.07  
% 4.09/1.07  fof(f54,plain,(
% 4.09/1.07    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.09/1.08    inference(cnf_transformation,[],[f25])).
% 4.09/1.08  
% 4.09/1.08  fof(f2,axiom,(
% 4.09/1.08    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.09/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.09/1.08  
% 4.09/1.08  fof(f29,plain,(
% 4.09/1.08    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.09/1.08    inference(nnf_transformation,[],[f2])).
% 4.09/1.08  
% 4.09/1.08  fof(f30,plain,(
% 4.09/1.08    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.09/1.08    inference(flattening,[],[f29])).
% 4.09/1.08  
% 4.09/1.08  fof(f38,plain,(
% 4.09/1.08    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.09/1.08    inference(cnf_transformation,[],[f30])).
% 4.09/1.08  
% 4.09/1.08  fof(f48,plain,(
% 4.09/1.08    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.09/1.08    inference(cnf_transformation,[],[f32])).
% 4.09/1.08  
% 4.09/1.08  fof(f71,plain,(
% 4.09/1.08    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.09/1.08    inference(equality_resolution,[],[f48])).
% 4.09/1.08  
% 4.09/1.08  fof(f59,plain,(
% 4.09/1.08    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 4.09/1.08    inference(cnf_transformation,[],[f34])).
% 4.09/1.08  
% 4.09/1.08  cnf(c_17,negated_conjecture,
% 4.09/1.08      ( v1_relat_1(sK0) ),
% 4.09/1.08      inference(cnf_transformation,[],[f58]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_359,plain,
% 4.09/1.08      ( v1_relat_1(sK0) = iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_0,plain,
% 4.09/1.08      ( v1_xboole_0(k1_xboole_0) ),
% 4.09/1.08      inference(cnf_transformation,[],[f35]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_368,plain,
% 4.09/1.08      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_9,plain,
% 4.09/1.08      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 4.09/1.08      inference(cnf_transformation,[],[f51]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_364,plain,
% 4.09/1.08      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_894,plain,
% 4.09/1.08      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_368,c_364]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_10,plain,
% 4.09/1.08      ( ~ v1_relat_1(X0)
% 4.09/1.08      | ~ v1_relat_1(X1)
% 4.09/1.08      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 4.09/1.08      inference(cnf_transformation,[],[f52]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_363,plain,
% 4.09/1.08      ( v1_relat_1(X0) != iProver_top
% 4.09/1.08      | v1_relat_1(X1) != iProver_top
% 4.09/1.08      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_11,plain,
% 4.09/1.08      ( ~ v1_relat_1(X0)
% 4.09/1.08      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 4.09/1.08      inference(cnf_transformation,[],[f67]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_362,plain,
% 4.09/1.08      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 4.09/1.08      | v1_relat_1(X0) != iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1127,plain,
% 4.09/1.08      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 4.09/1.08      | v1_relat_1(X1) != iProver_top
% 4.09/1.08      | v1_relat_1(X0) != iProver_top ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_363,c_362]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1887,plain,
% 4.09/1.08      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
% 4.09/1.08      | v1_relat_1(X0) != iProver_top ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_894,c_1127]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_6992,plain,
% 4.09/1.08      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_359,c_1887]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_15,plain,
% 4.09/1.08      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.09/1.08      inference(cnf_transformation,[],[f56]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_13,plain,
% 4.09/1.08      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 4.09/1.08      | ~ v1_relat_1(X1)
% 4.09/1.08      | ~ v1_relat_1(X0)
% 4.09/1.08      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 4.09/1.08      inference(cnf_transformation,[],[f55]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_360,plain,
% 4.09/1.08      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 4.09/1.08      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) != iProver_top
% 4.09/1.08      | v1_relat_1(X0) != iProver_top
% 4.09/1.08      | v1_relat_1(X1) != iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_513,plain,
% 4.09/1.08      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 4.09/1.08      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 4.09/1.08      | v1_relat_1(X0) != iProver_top
% 4.09/1.08      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_15,c_360]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_14,plain,
% 4.09/1.08      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.09/1.08      inference(cnf_transformation,[],[f57]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_527,plain,
% 4.09/1.08      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 4.09/1.08      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 4.09/1.08      | v1_relat_1(X0) != iProver_top
% 4.09/1.08      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.09/1.08      inference(light_normalisation,[status(thm)],[c_513,c_14]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_31,plain,
% 4.09/1.08      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_33,plain,
% 4.09/1.08      ( v1_relat_1(k1_xboole_0) = iProver_top
% 4.09/1.08      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 4.09/1.08      inference(instantiation,[status(thm)],[c_31]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_45,plain,
% 4.09/1.08      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1236,plain,
% 4.09/1.08      ( v1_relat_1(X0) != iProver_top
% 4.09/1.08      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 4.09/1.08      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.09/1.08      inference(global_propositional_subsumption,
% 4.09/1.08                [status(thm)],
% 4.09/1.08                [c_527,c_33,c_45]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1237,plain,
% 4.09/1.08      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 4.09/1.08      | r1_tarski(k1_xboole_0,k2_relat_1(X0)) != iProver_top
% 4.09/1.08      | v1_relat_1(X0) != iProver_top ),
% 4.09/1.08      inference(renaming,[status(thm)],[c_1236]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_5,plain,
% 4.09/1.08      ( r1_tarski(k1_xboole_0,X0) ),
% 4.09/1.08      inference(cnf_transformation,[],[f40]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_365,plain,
% 4.09/1.08      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1243,plain,
% 4.09/1.08      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 4.09/1.08      | v1_relat_1(X0) != iProver_top ),
% 4.09/1.08      inference(forward_subsumption_resolution,
% 4.09/1.08                [status(thm)],
% 4.09/1.08                [c_1237,c_365]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1248,plain,
% 4.09/1.08      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_359,c_1243]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_6999,plain,
% 4.09/1.08      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 4.09/1.08      inference(light_normalisation,[status(thm)],[c_6992,c_1248]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_4,plain,
% 4.09/1.08      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.09/1.08      inference(cnf_transformation,[],[f66]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_6,plain,
% 4.09/1.08      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.09/1.08      inference(cnf_transformation,[],[f70]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_7000,plain,
% 4.09/1.08      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 4.09/1.08      inference(demodulation,[status(thm)],[c_6999,c_4,c_6]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1886,plain,
% 4.09/1.08      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) = k5_relat_1(X0,sK0)
% 4.09/1.08      | v1_relat_1(X0) != iProver_top ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_359,c_1127]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_6262,plain,
% 4.09/1.08      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_894,c_1886]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_12,plain,
% 4.09/1.08      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 4.09/1.08      | ~ v1_relat_1(X1)
% 4.09/1.08      | ~ v1_relat_1(X0) ),
% 4.09/1.08      inference(cnf_transformation,[],[f54]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_361,plain,
% 4.09/1.08      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 4.09/1.08      | v1_relat_1(X1) != iProver_top
% 4.09/1.08      | v1_relat_1(X0) != iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_799,plain,
% 4.09/1.08      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 4.09/1.08      | v1_relat_1(X0) != iProver_top
% 4.09/1.08      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_15,c_361]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1132,plain,
% 4.09/1.08      ( v1_relat_1(X0) != iProver_top
% 4.09/1.08      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 4.09/1.08      inference(global_propositional_subsumption,
% 4.09/1.08                [status(thm)],
% 4.09/1.08                [c_799,c_33,c_45]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1133,plain,
% 4.09/1.08      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 4.09/1.08      | v1_relat_1(X0) != iProver_top ),
% 4.09/1.08      inference(renaming,[status(thm)],[c_1132]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1,plain,
% 4.09/1.08      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.09/1.08      inference(cnf_transformation,[],[f38]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_367,plain,
% 4.09/1.08      ( X0 = X1
% 4.09/1.08      | r1_tarski(X0,X1) != iProver_top
% 4.09/1.08      | r1_tarski(X1,X0) != iProver_top ),
% 4.09/1.08      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1020,plain,
% 4.09/1.08      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_365,c_367]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_1477,plain,
% 4.09/1.08      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 4.09/1.08      | v1_relat_1(X0) != iProver_top ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_1133,c_1020]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_3737,plain,
% 4.09/1.08      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 4.09/1.08      inference(superposition,[status(thm)],[c_359,c_1477]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_6264,plain,
% 4.09/1.08      ( k1_setfam_1(k6_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 4.09/1.08      inference(light_normalisation,[status(thm)],[c_6262,c_3737]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_7,plain,
% 4.09/1.08      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.09/1.08      inference(cnf_transformation,[],[f71]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_6265,plain,
% 4.09/1.08      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 4.09/1.08      inference(demodulation,[status(thm)],[c_6264,c_4,c_7]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_16,negated_conjecture,
% 4.09/1.08      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 4.09/1.08      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 4.09/1.08      inference(cnf_transformation,[],[f59]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_6386,plain,
% 4.09/1.08      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 4.09/1.08      | k1_xboole_0 != k1_xboole_0 ),
% 4.09/1.08      inference(demodulation,[status(thm)],[c_6265,c_16]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(c_6387,plain,
% 4.09/1.08      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 4.09/1.08      inference(equality_resolution_simp,[status(thm)],[c_6386]) ).
% 4.09/1.08  
% 4.09/1.08  cnf(contradiction,plain,
% 4.09/1.08      ( $false ),
% 4.09/1.08      inference(minisat,[status(thm)],[c_7000,c_6387]) ).
% 4.09/1.08  
% 4.09/1.08  
% 4.09/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 4.09/1.08  
% 4.09/1.08  ------                               Statistics
% 4.09/1.08  
% 4.09/1.08  ------ Selected
% 4.09/1.08  
% 4.09/1.08  total_time:                             0.27
% 4.09/1.08  
%------------------------------------------------------------------------------
