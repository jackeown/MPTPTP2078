%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:59 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 258 expanded)
%              Number of clauses        :   60 (  93 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  248 ( 478 expanded)
%              Number of equality atoms :  144 ( 278 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f31,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f34])).

fof(f57,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f61])).

fof(f64,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f41,f62])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_442,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_454,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_447,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_923,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_454,c_447])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_446,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_445,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1261,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_445])).

cnf(c_3024,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_1261])).

cnf(c_9896,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_442,c_3024])).

cnf(c_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_12,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_444,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_916,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_444])).

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

cnf(c_1266,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_916,c_33,c_50])).

cnf(c_1267,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1266])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_450,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_452,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1145,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_452])).

cnf(c_1700,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1145])).

cnf(c_6589,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_442,c_1700])).

cnf(c_9913,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_9896,c_6589])).

cnf(c_5,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_449,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_453,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1043,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_449,c_453])).

cnf(c_2038,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_1043])).

cnf(c_9914,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9913,c_5,c_2038])).

cnf(c_3023,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) = k5_relat_1(X0,sK0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_442,c_1261])).

cnf(c_9524,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_923,c_3023])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_443,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_610,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_443])).

cnf(c_15,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_624,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_610,c_15])).

cnf(c_1444,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_33,c_50])).

cnf(c_1445,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1444])).

cnf(c_1451,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1445,c_450])).

cnf(c_1456,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_442,c_1451])).

cnf(c_9536,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_9524,c_1456])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_448,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1024,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_453])).

cnf(c_1926,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_454,c_1024])).

cnf(c_9537,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9536,c_5,c_1926])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9557,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9537,c_16])).

cnf(c_9558,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9557])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9914,c_9558])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:13:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.64/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/0.97  
% 3.64/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.64/0.97  
% 3.64/0.97  ------  iProver source info
% 3.64/0.97  
% 3.64/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.64/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.64/0.97  git: non_committed_changes: false
% 3.64/0.97  git: last_make_outside_of_git: false
% 3.64/0.97  
% 3.64/0.97  ------ 
% 3.64/0.97  
% 3.64/0.97  ------ Input Options
% 3.64/0.97  
% 3.64/0.97  --out_options                           all
% 3.64/0.97  --tptp_safe_out                         true
% 3.64/0.97  --problem_path                          ""
% 3.64/0.97  --include_path                          ""
% 3.64/0.97  --clausifier                            res/vclausify_rel
% 3.64/0.97  --clausifier_options                    --mode clausify
% 3.64/0.97  --stdin                                 false
% 3.64/0.97  --stats_out                             sel
% 3.64/0.97  
% 3.64/0.97  ------ General Options
% 3.64/0.97  
% 3.64/0.97  --fof                                   false
% 3.64/0.97  --time_out_real                         604.99
% 3.64/0.97  --time_out_virtual                      -1.
% 3.64/0.97  --symbol_type_check                     false
% 3.64/0.97  --clausify_out                          false
% 3.64/0.97  --sig_cnt_out                           false
% 3.64/0.97  --trig_cnt_out                          false
% 3.64/0.97  --trig_cnt_out_tolerance                1.
% 3.64/0.97  --trig_cnt_out_sk_spl                   false
% 3.64/0.97  --abstr_cl_out                          false
% 3.64/0.97  
% 3.64/0.97  ------ Global Options
% 3.64/0.97  
% 3.64/0.97  --schedule                              none
% 3.64/0.97  --add_important_lit                     false
% 3.64/0.97  --prop_solver_per_cl                    1000
% 3.64/0.97  --min_unsat_core                        false
% 3.64/0.97  --soft_assumptions                      false
% 3.64/0.97  --soft_lemma_size                       3
% 3.64/0.97  --prop_impl_unit_size                   0
% 3.64/0.97  --prop_impl_unit                        []
% 3.64/0.97  --share_sel_clauses                     true
% 3.64/0.97  --reset_solvers                         false
% 3.64/0.97  --bc_imp_inh                            [conj_cone]
% 3.64/0.97  --conj_cone_tolerance                   3.
% 3.64/0.97  --extra_neg_conj                        none
% 3.64/0.97  --large_theory_mode                     true
% 3.64/0.97  --prolific_symb_bound                   200
% 3.64/0.97  --lt_threshold                          2000
% 3.64/0.97  --clause_weak_htbl                      true
% 3.64/0.97  --gc_record_bc_elim                     false
% 3.64/0.97  
% 3.64/0.97  ------ Preprocessing Options
% 3.64/0.97  
% 3.64/0.97  --preprocessing_flag                    true
% 3.64/0.97  --time_out_prep_mult                    0.1
% 3.64/0.97  --splitting_mode                        input
% 3.64/0.97  --splitting_grd                         true
% 3.64/0.97  --splitting_cvd                         false
% 3.64/0.97  --splitting_cvd_svl                     false
% 3.64/0.97  --splitting_nvd                         32
% 3.64/0.97  --sub_typing                            true
% 3.64/0.97  --prep_gs_sim                           false
% 3.64/0.97  --prep_unflatten                        true
% 3.64/0.97  --prep_res_sim                          true
% 3.64/0.97  --prep_upred                            true
% 3.64/0.97  --prep_sem_filter                       exhaustive
% 3.64/0.97  --prep_sem_filter_out                   false
% 3.64/0.97  --pred_elim                             false
% 3.64/0.97  --res_sim_input                         true
% 3.64/0.97  --eq_ax_congr_red                       true
% 3.64/0.97  --pure_diseq_elim                       true
% 3.64/0.97  --brand_transform                       false
% 3.64/0.97  --non_eq_to_eq                          false
% 3.64/0.97  --prep_def_merge                        true
% 3.64/0.97  --prep_def_merge_prop_impl              false
% 3.64/0.98  --prep_def_merge_mbd                    true
% 3.64/0.98  --prep_def_merge_tr_red                 false
% 3.64/0.98  --prep_def_merge_tr_cl                  false
% 3.64/0.98  --smt_preprocessing                     true
% 3.64/0.98  --smt_ac_axioms                         fast
% 3.64/0.98  --preprocessed_out                      false
% 3.64/0.98  --preprocessed_stats                    false
% 3.64/0.98  
% 3.64/0.98  ------ Abstraction refinement Options
% 3.64/0.98  
% 3.64/0.98  --abstr_ref                             []
% 3.64/0.98  --abstr_ref_prep                        false
% 3.64/0.98  --abstr_ref_until_sat                   false
% 3.64/0.98  --abstr_ref_sig_restrict                funpre
% 3.64/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.98  --abstr_ref_under                       []
% 3.64/0.98  
% 3.64/0.98  ------ SAT Options
% 3.64/0.98  
% 3.64/0.98  --sat_mode                              false
% 3.64/0.98  --sat_fm_restart_options                ""
% 3.64/0.98  --sat_gr_def                            false
% 3.64/0.98  --sat_epr_types                         true
% 3.64/0.98  --sat_non_cyclic_types                  false
% 3.64/0.98  --sat_finite_models                     false
% 3.64/0.98  --sat_fm_lemmas                         false
% 3.64/0.98  --sat_fm_prep                           false
% 3.64/0.98  --sat_fm_uc_incr                        true
% 3.64/0.98  --sat_out_model                         small
% 3.64/0.98  --sat_out_clauses                       false
% 3.64/0.98  
% 3.64/0.98  ------ QBF Options
% 3.64/0.98  
% 3.64/0.98  --qbf_mode                              false
% 3.64/0.98  --qbf_elim_univ                         false
% 3.64/0.98  --qbf_dom_inst                          none
% 3.64/0.98  --qbf_dom_pre_inst                      false
% 3.64/0.98  --qbf_sk_in                             false
% 3.64/0.98  --qbf_pred_elim                         true
% 3.64/0.98  --qbf_split                             512
% 3.64/0.98  
% 3.64/0.98  ------ BMC1 Options
% 3.64/0.98  
% 3.64/0.98  --bmc1_incremental                      false
% 3.64/0.98  --bmc1_axioms                           reachable_all
% 3.64/0.98  --bmc1_min_bound                        0
% 3.64/0.98  --bmc1_max_bound                        -1
% 3.64/0.98  --bmc1_max_bound_default                -1
% 3.64/0.98  --bmc1_symbol_reachability              true
% 3.64/0.98  --bmc1_property_lemmas                  false
% 3.64/0.98  --bmc1_k_induction                      false
% 3.64/0.98  --bmc1_non_equiv_states                 false
% 3.64/0.98  --bmc1_deadlock                         false
% 3.64/0.98  --bmc1_ucm                              false
% 3.64/0.98  --bmc1_add_unsat_core                   none
% 3.64/0.98  --bmc1_unsat_core_children              false
% 3.64/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.98  --bmc1_out_stat                         full
% 3.64/0.98  --bmc1_ground_init                      false
% 3.64/0.98  --bmc1_pre_inst_next_state              false
% 3.64/0.98  --bmc1_pre_inst_state                   false
% 3.64/0.98  --bmc1_pre_inst_reach_state             false
% 3.64/0.98  --bmc1_out_unsat_core                   false
% 3.64/0.98  --bmc1_aig_witness_out                  false
% 3.64/0.98  --bmc1_verbose                          false
% 3.64/0.98  --bmc1_dump_clauses_tptp                false
% 3.64/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.98  --bmc1_dump_file                        -
% 3.64/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.98  --bmc1_ucm_extend_mode                  1
% 3.64/0.98  --bmc1_ucm_init_mode                    2
% 3.64/0.98  --bmc1_ucm_cone_mode                    none
% 3.64/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.98  --bmc1_ucm_relax_model                  4
% 3.64/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.98  --bmc1_ucm_layered_model                none
% 3.64/0.98  --bmc1_ucm_max_lemma_size               10
% 3.64/0.98  
% 3.64/0.98  ------ AIG Options
% 3.64/0.98  
% 3.64/0.98  --aig_mode                              false
% 3.64/0.98  
% 3.64/0.98  ------ Instantiation Options
% 3.64/0.98  
% 3.64/0.98  --instantiation_flag                    true
% 3.64/0.98  --inst_sos_flag                         false
% 3.64/0.98  --inst_sos_phase                        true
% 3.64/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.98  --inst_lit_sel_side                     num_symb
% 3.64/0.98  --inst_solver_per_active                1400
% 3.64/0.98  --inst_solver_calls_frac                1.
% 3.64/0.98  --inst_passive_queue_type               priority_queues
% 3.64/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.98  --inst_passive_queues_freq              [25;2]
% 3.64/0.98  --inst_dismatching                      true
% 3.64/0.98  --inst_eager_unprocessed_to_passive     true
% 3.64/0.98  --inst_prop_sim_given                   true
% 3.64/0.98  --inst_prop_sim_new                     false
% 3.64/0.98  --inst_subs_new                         false
% 3.64/0.98  --inst_eq_res_simp                      false
% 3.64/0.98  --inst_subs_given                       false
% 3.64/0.98  --inst_orphan_elimination               true
% 3.64/0.98  --inst_learning_loop_flag               true
% 3.64/0.98  --inst_learning_start                   3000
% 3.64/0.98  --inst_learning_factor                  2
% 3.64/0.98  --inst_start_prop_sim_after_learn       3
% 3.64/0.98  --inst_sel_renew                        solver
% 3.64/0.98  --inst_lit_activity_flag                true
% 3.64/0.98  --inst_restr_to_given                   false
% 3.64/0.98  --inst_activity_threshold               500
% 3.64/0.98  --inst_out_proof                        true
% 3.64/0.98  
% 3.64/0.98  ------ Resolution Options
% 3.64/0.98  
% 3.64/0.98  --resolution_flag                       true
% 3.64/0.98  --res_lit_sel                           adaptive
% 3.64/0.98  --res_lit_sel_side                      none
% 3.64/0.98  --res_ordering                          kbo
% 3.64/0.98  --res_to_prop_solver                    active
% 3.64/0.98  --res_prop_simpl_new                    false
% 3.64/0.98  --res_prop_simpl_given                  true
% 3.64/0.98  --res_passive_queue_type                priority_queues
% 3.64/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.98  --res_passive_queues_freq               [15;5]
% 3.64/0.98  --res_forward_subs                      full
% 3.64/0.98  --res_backward_subs                     full
% 3.64/0.98  --res_forward_subs_resolution           true
% 3.64/0.98  --res_backward_subs_resolution          true
% 3.64/0.98  --res_orphan_elimination                true
% 3.64/0.98  --res_time_limit                        2.
% 3.64/0.98  --res_out_proof                         true
% 3.64/0.98  
% 3.64/0.98  ------ Superposition Options
% 3.64/0.98  
% 3.64/0.98  --superposition_flag                    true
% 3.64/0.98  --sup_passive_queue_type                priority_queues
% 3.64/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.98  --sup_passive_queues_freq               [1;4]
% 3.64/0.98  --demod_completeness_check              fast
% 3.64/0.98  --demod_use_ground                      true
% 3.64/0.98  --sup_to_prop_solver                    passive
% 3.64/0.98  --sup_prop_simpl_new                    true
% 3.64/0.98  --sup_prop_simpl_given                  true
% 3.64/0.98  --sup_fun_splitting                     false
% 3.64/0.98  --sup_smt_interval                      50000
% 3.64/0.98  
% 3.64/0.98  ------ Superposition Simplification Setup
% 3.64/0.98  
% 3.64/0.98  --sup_indices_passive                   []
% 3.64/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_full_bw                           [BwDemod]
% 3.64/0.98  --sup_immed_triv                        [TrivRules]
% 3.64/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_immed_bw_main                     []
% 3.64/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.98  
% 3.64/0.98  ------ Combination Options
% 3.64/0.98  
% 3.64/0.98  --comb_res_mult                         3
% 3.64/0.98  --comb_sup_mult                         2
% 3.64/0.98  --comb_inst_mult                        10
% 3.64/0.98  
% 3.64/0.98  ------ Debug Options
% 3.64/0.98  
% 3.64/0.98  --dbg_backtrace                         false
% 3.64/0.98  --dbg_dump_prop_clauses                 false
% 3.64/0.98  --dbg_dump_prop_clauses_file            -
% 3.64/0.98  --dbg_out_stat                          false
% 3.64/0.98  ------ Parsing...
% 3.64/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.64/0.98  ------ Proving...
% 3.64/0.98  ------ Problem Properties 
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  clauses                                 17
% 3.64/0.98  conjectures                             2
% 3.64/0.98  EPR                                     7
% 3.64/0.98  Horn                                    17
% 3.64/0.98  unary                                   7
% 3.64/0.98  binary                                  6
% 3.64/0.98  lits                                    32
% 3.64/0.98  lits eq                                 9
% 3.64/0.98  fd_pure                                 0
% 3.64/0.98  fd_pseudo                               0
% 3.64/0.98  fd_cond                                 1
% 3.64/0.98  fd_pseudo_cond                          1
% 3.64/0.98  AC symbols                              0
% 3.64/0.98  
% 3.64/0.98  ------ Input Options Time Limit: Unbounded
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  ------ 
% 3.64/0.98  Current options:
% 3.64/0.98  ------ 
% 3.64/0.98  
% 3.64/0.98  ------ Input Options
% 3.64/0.98  
% 3.64/0.98  --out_options                           all
% 3.64/0.98  --tptp_safe_out                         true
% 3.64/0.98  --problem_path                          ""
% 3.64/0.98  --include_path                          ""
% 3.64/0.98  --clausifier                            res/vclausify_rel
% 3.64/0.98  --clausifier_options                    --mode clausify
% 3.64/0.98  --stdin                                 false
% 3.64/0.98  --stats_out                             sel
% 3.64/0.98  
% 3.64/0.98  ------ General Options
% 3.64/0.98  
% 3.64/0.98  --fof                                   false
% 3.64/0.98  --time_out_real                         604.99
% 3.64/0.98  --time_out_virtual                      -1.
% 3.64/0.98  --symbol_type_check                     false
% 3.64/0.98  --clausify_out                          false
% 3.64/0.98  --sig_cnt_out                           false
% 3.64/0.98  --trig_cnt_out                          false
% 3.64/0.98  --trig_cnt_out_tolerance                1.
% 3.64/0.98  --trig_cnt_out_sk_spl                   false
% 3.64/0.98  --abstr_cl_out                          false
% 3.64/0.98  
% 3.64/0.98  ------ Global Options
% 3.64/0.98  
% 3.64/0.98  --schedule                              none
% 3.64/0.98  --add_important_lit                     false
% 3.64/0.98  --prop_solver_per_cl                    1000
% 3.64/0.98  --min_unsat_core                        false
% 3.64/0.98  --soft_assumptions                      false
% 3.64/0.98  --soft_lemma_size                       3
% 3.64/0.98  --prop_impl_unit_size                   0
% 3.64/0.98  --prop_impl_unit                        []
% 3.64/0.98  --share_sel_clauses                     true
% 3.64/0.98  --reset_solvers                         false
% 3.64/0.98  --bc_imp_inh                            [conj_cone]
% 3.64/0.98  --conj_cone_tolerance                   3.
% 3.64/0.98  --extra_neg_conj                        none
% 3.64/0.98  --large_theory_mode                     true
% 3.64/0.98  --prolific_symb_bound                   200
% 3.64/0.98  --lt_threshold                          2000
% 3.64/0.98  --clause_weak_htbl                      true
% 3.64/0.98  --gc_record_bc_elim                     false
% 3.64/0.98  
% 3.64/0.98  ------ Preprocessing Options
% 3.64/0.98  
% 3.64/0.98  --preprocessing_flag                    true
% 3.64/0.98  --time_out_prep_mult                    0.1
% 3.64/0.98  --splitting_mode                        input
% 3.64/0.98  --splitting_grd                         true
% 3.64/0.98  --splitting_cvd                         false
% 3.64/0.98  --splitting_cvd_svl                     false
% 3.64/0.98  --splitting_nvd                         32
% 3.64/0.98  --sub_typing                            true
% 3.64/0.98  --prep_gs_sim                           false
% 3.64/0.98  --prep_unflatten                        true
% 3.64/0.98  --prep_res_sim                          true
% 3.64/0.98  --prep_upred                            true
% 3.64/0.98  --prep_sem_filter                       exhaustive
% 3.64/0.98  --prep_sem_filter_out                   false
% 3.64/0.98  --pred_elim                             false
% 3.64/0.98  --res_sim_input                         true
% 3.64/0.98  --eq_ax_congr_red                       true
% 3.64/0.98  --pure_diseq_elim                       true
% 3.64/0.98  --brand_transform                       false
% 3.64/0.98  --non_eq_to_eq                          false
% 3.64/0.98  --prep_def_merge                        true
% 3.64/0.98  --prep_def_merge_prop_impl              false
% 3.64/0.98  --prep_def_merge_mbd                    true
% 3.64/0.98  --prep_def_merge_tr_red                 false
% 3.64/0.98  --prep_def_merge_tr_cl                  false
% 3.64/0.98  --smt_preprocessing                     true
% 3.64/0.98  --smt_ac_axioms                         fast
% 3.64/0.98  --preprocessed_out                      false
% 3.64/0.98  --preprocessed_stats                    false
% 3.64/0.98  
% 3.64/0.98  ------ Abstraction refinement Options
% 3.64/0.98  
% 3.64/0.98  --abstr_ref                             []
% 3.64/0.98  --abstr_ref_prep                        false
% 3.64/0.98  --abstr_ref_until_sat                   false
% 3.64/0.98  --abstr_ref_sig_restrict                funpre
% 3.64/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.64/0.98  --abstr_ref_under                       []
% 3.64/0.98  
% 3.64/0.98  ------ SAT Options
% 3.64/0.98  
% 3.64/0.98  --sat_mode                              false
% 3.64/0.98  --sat_fm_restart_options                ""
% 3.64/0.98  --sat_gr_def                            false
% 3.64/0.98  --sat_epr_types                         true
% 3.64/0.98  --sat_non_cyclic_types                  false
% 3.64/0.98  --sat_finite_models                     false
% 3.64/0.98  --sat_fm_lemmas                         false
% 3.64/0.98  --sat_fm_prep                           false
% 3.64/0.98  --sat_fm_uc_incr                        true
% 3.64/0.98  --sat_out_model                         small
% 3.64/0.98  --sat_out_clauses                       false
% 3.64/0.98  
% 3.64/0.98  ------ QBF Options
% 3.64/0.98  
% 3.64/0.98  --qbf_mode                              false
% 3.64/0.98  --qbf_elim_univ                         false
% 3.64/0.98  --qbf_dom_inst                          none
% 3.64/0.98  --qbf_dom_pre_inst                      false
% 3.64/0.98  --qbf_sk_in                             false
% 3.64/0.98  --qbf_pred_elim                         true
% 3.64/0.98  --qbf_split                             512
% 3.64/0.98  
% 3.64/0.98  ------ BMC1 Options
% 3.64/0.98  
% 3.64/0.98  --bmc1_incremental                      false
% 3.64/0.98  --bmc1_axioms                           reachable_all
% 3.64/0.98  --bmc1_min_bound                        0
% 3.64/0.98  --bmc1_max_bound                        -1
% 3.64/0.98  --bmc1_max_bound_default                -1
% 3.64/0.98  --bmc1_symbol_reachability              true
% 3.64/0.98  --bmc1_property_lemmas                  false
% 3.64/0.98  --bmc1_k_induction                      false
% 3.64/0.98  --bmc1_non_equiv_states                 false
% 3.64/0.98  --bmc1_deadlock                         false
% 3.64/0.98  --bmc1_ucm                              false
% 3.64/0.98  --bmc1_add_unsat_core                   none
% 3.64/0.98  --bmc1_unsat_core_children              false
% 3.64/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.64/0.98  --bmc1_out_stat                         full
% 3.64/0.98  --bmc1_ground_init                      false
% 3.64/0.98  --bmc1_pre_inst_next_state              false
% 3.64/0.98  --bmc1_pre_inst_state                   false
% 3.64/0.98  --bmc1_pre_inst_reach_state             false
% 3.64/0.98  --bmc1_out_unsat_core                   false
% 3.64/0.98  --bmc1_aig_witness_out                  false
% 3.64/0.98  --bmc1_verbose                          false
% 3.64/0.98  --bmc1_dump_clauses_tptp                false
% 3.64/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.64/0.98  --bmc1_dump_file                        -
% 3.64/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.64/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.64/0.98  --bmc1_ucm_extend_mode                  1
% 3.64/0.98  --bmc1_ucm_init_mode                    2
% 3.64/0.98  --bmc1_ucm_cone_mode                    none
% 3.64/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.64/0.98  --bmc1_ucm_relax_model                  4
% 3.64/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.64/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.64/0.98  --bmc1_ucm_layered_model                none
% 3.64/0.98  --bmc1_ucm_max_lemma_size               10
% 3.64/0.98  
% 3.64/0.98  ------ AIG Options
% 3.64/0.98  
% 3.64/0.98  --aig_mode                              false
% 3.64/0.98  
% 3.64/0.98  ------ Instantiation Options
% 3.64/0.98  
% 3.64/0.98  --instantiation_flag                    true
% 3.64/0.98  --inst_sos_flag                         false
% 3.64/0.98  --inst_sos_phase                        true
% 3.64/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.64/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.64/0.98  --inst_lit_sel_side                     num_symb
% 3.64/0.98  --inst_solver_per_active                1400
% 3.64/0.98  --inst_solver_calls_frac                1.
% 3.64/0.98  --inst_passive_queue_type               priority_queues
% 3.64/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.64/0.98  --inst_passive_queues_freq              [25;2]
% 3.64/0.98  --inst_dismatching                      true
% 3.64/0.98  --inst_eager_unprocessed_to_passive     true
% 3.64/0.98  --inst_prop_sim_given                   true
% 3.64/0.98  --inst_prop_sim_new                     false
% 3.64/0.98  --inst_subs_new                         false
% 3.64/0.98  --inst_eq_res_simp                      false
% 3.64/0.98  --inst_subs_given                       false
% 3.64/0.98  --inst_orphan_elimination               true
% 3.64/0.98  --inst_learning_loop_flag               true
% 3.64/0.98  --inst_learning_start                   3000
% 3.64/0.98  --inst_learning_factor                  2
% 3.64/0.98  --inst_start_prop_sim_after_learn       3
% 3.64/0.98  --inst_sel_renew                        solver
% 3.64/0.98  --inst_lit_activity_flag                true
% 3.64/0.98  --inst_restr_to_given                   false
% 3.64/0.98  --inst_activity_threshold               500
% 3.64/0.98  --inst_out_proof                        true
% 3.64/0.98  
% 3.64/0.98  ------ Resolution Options
% 3.64/0.98  
% 3.64/0.98  --resolution_flag                       true
% 3.64/0.98  --res_lit_sel                           adaptive
% 3.64/0.98  --res_lit_sel_side                      none
% 3.64/0.98  --res_ordering                          kbo
% 3.64/0.98  --res_to_prop_solver                    active
% 3.64/0.98  --res_prop_simpl_new                    false
% 3.64/0.98  --res_prop_simpl_given                  true
% 3.64/0.98  --res_passive_queue_type                priority_queues
% 3.64/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.64/0.98  --res_passive_queues_freq               [15;5]
% 3.64/0.98  --res_forward_subs                      full
% 3.64/0.98  --res_backward_subs                     full
% 3.64/0.98  --res_forward_subs_resolution           true
% 3.64/0.98  --res_backward_subs_resolution          true
% 3.64/0.98  --res_orphan_elimination                true
% 3.64/0.98  --res_time_limit                        2.
% 3.64/0.98  --res_out_proof                         true
% 3.64/0.98  
% 3.64/0.98  ------ Superposition Options
% 3.64/0.98  
% 3.64/0.98  --superposition_flag                    true
% 3.64/0.98  --sup_passive_queue_type                priority_queues
% 3.64/0.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.64/0.98  --sup_passive_queues_freq               [1;4]
% 3.64/0.98  --demod_completeness_check              fast
% 3.64/0.98  --demod_use_ground                      true
% 3.64/0.98  --sup_to_prop_solver                    passive
% 3.64/0.98  --sup_prop_simpl_new                    true
% 3.64/0.98  --sup_prop_simpl_given                  true
% 3.64/0.98  --sup_fun_splitting                     false
% 3.64/0.98  --sup_smt_interval                      50000
% 3.64/0.98  
% 3.64/0.98  ------ Superposition Simplification Setup
% 3.64/0.98  
% 3.64/0.98  --sup_indices_passive                   []
% 3.64/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.64/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.64/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_full_bw                           [BwDemod]
% 3.64/0.98  --sup_immed_triv                        [TrivRules]
% 3.64/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.64/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_immed_bw_main                     []
% 3.64/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.64/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.64/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.64/0.98  
% 3.64/0.98  ------ Combination Options
% 3.64/0.98  
% 3.64/0.98  --comb_res_mult                         3
% 3.64/0.98  --comb_sup_mult                         2
% 3.64/0.98  --comb_inst_mult                        10
% 3.64/0.98  
% 3.64/0.98  ------ Debug Options
% 3.64/0.98  
% 3.64/0.98  --dbg_backtrace                         false
% 3.64/0.98  --dbg_dump_prop_clauses                 false
% 3.64/0.98  --dbg_dump_prop_clauses_file            -
% 3.64/0.98  --dbg_out_stat                          false
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  ------ Proving...
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  % SZS status Theorem for theBenchmark.p
% 3.64/0.98  
% 3.64/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.64/0.98  
% 3.64/0.98  fof(f19,conjecture,(
% 3.64/0.98    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f20,negated_conjecture,(
% 3.64/0.98    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.64/0.98    inference(negated_conjecture,[],[f19])).
% 3.64/0.98  
% 3.64/0.98  fof(f31,plain,(
% 3.64/0.98    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.64/0.98    inference(ennf_transformation,[],[f20])).
% 3.64/0.98  
% 3.64/0.98  fof(f34,plain,(
% 3.64/0.98    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 3.64/0.98    introduced(choice_axiom,[])).
% 3.64/0.98  
% 3.64/0.98  fof(f35,plain,(
% 3.64/0.98    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 3.64/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f34])).
% 3.64/0.98  
% 3.64/0.98  fof(f57,plain,(
% 3.64/0.98    v1_relat_1(sK0)),
% 3.64/0.98    inference(cnf_transformation,[],[f35])).
% 3.64/0.98  
% 3.64/0.98  fof(f1,axiom,(
% 3.64/0.98    v1_xboole_0(k1_xboole_0)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f36,plain,(
% 3.64/0.98    v1_xboole_0(k1_xboole_0)),
% 3.64/0.98    inference(cnf_transformation,[],[f1])).
% 3.64/0.98  
% 3.64/0.98  fof(f13,axiom,(
% 3.64/0.98    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f24,plain,(
% 3.64/0.98    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.64/0.98    inference(ennf_transformation,[],[f13])).
% 3.64/0.98  
% 3.64/0.98  fof(f50,plain,(
% 3.64/0.98    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f24])).
% 3.64/0.98  
% 3.64/0.98  fof(f14,axiom,(
% 3.64/0.98    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f25,plain,(
% 3.64/0.98    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.64/0.98    inference(ennf_transformation,[],[f14])).
% 3.64/0.98  
% 3.64/0.98  fof(f26,plain,(
% 3.64/0.98    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.64/0.98    inference(flattening,[],[f25])).
% 3.64/0.98  
% 3.64/0.98  fof(f51,plain,(
% 3.64/0.98    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f26])).
% 3.64/0.98  
% 3.64/0.98  fof(f15,axiom,(
% 3.64/0.98    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f27,plain,(
% 3.64/0.98    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.64/0.98    inference(ennf_transformation,[],[f15])).
% 3.64/0.98  
% 3.64/0.98  fof(f52,plain,(
% 3.64/0.98    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f27])).
% 3.64/0.98  
% 3.64/0.98  fof(f12,axiom,(
% 3.64/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f49,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.64/0.98    inference(cnf_transformation,[],[f12])).
% 3.64/0.98  
% 3.64/0.98  fof(f6,axiom,(
% 3.64/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f43,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f6])).
% 3.64/0.98  
% 3.64/0.98  fof(f7,axiom,(
% 3.64/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f44,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f7])).
% 3.64/0.98  
% 3.64/0.98  fof(f8,axiom,(
% 3.64/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f45,plain,(
% 3.64/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f8])).
% 3.64/0.98  
% 3.64/0.98  fof(f9,axiom,(
% 3.64/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f46,plain,(
% 3.64/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f9])).
% 3.64/0.98  
% 3.64/0.98  fof(f59,plain,(
% 3.64/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.64/0.98    inference(definition_unfolding,[],[f45,f46])).
% 3.64/0.98  
% 3.64/0.98  fof(f60,plain,(
% 3.64/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.64/0.98    inference(definition_unfolding,[],[f44,f59])).
% 3.64/0.98  
% 3.64/0.98  fof(f61,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.64/0.98    inference(definition_unfolding,[],[f43,f60])).
% 3.64/0.98  
% 3.64/0.98  fof(f62,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.64/0.98    inference(definition_unfolding,[],[f49,f61])).
% 3.64/0.98  
% 3.64/0.98  fof(f64,plain,(
% 3.64/0.98    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 3.64/0.98    inference(definition_unfolding,[],[f52,f62])).
% 3.64/0.98  
% 3.64/0.98  fof(f18,axiom,(
% 3.64/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f56,plain,(
% 3.64/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.64/0.98    inference(cnf_transformation,[],[f18])).
% 3.64/0.98  
% 3.64/0.98  fof(f16,axiom,(
% 3.64/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f28,plain,(
% 3.64/0.98    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.64/0.98    inference(ennf_transformation,[],[f16])).
% 3.64/0.98  
% 3.64/0.98  fof(f53,plain,(
% 3.64/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f28])).
% 3.64/0.98  
% 3.64/0.98  fof(f5,axiom,(
% 3.64/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f42,plain,(
% 3.64/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f5])).
% 3.64/0.98  
% 3.64/0.98  fof(f3,axiom,(
% 3.64/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f32,plain,(
% 3.64/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/0.98    inference(nnf_transformation,[],[f3])).
% 3.64/0.98  
% 3.64/0.98  fof(f33,plain,(
% 3.64/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.64/0.98    inference(flattening,[],[f32])).
% 3.64/0.98  
% 3.64/0.98  fof(f40,plain,(
% 3.64/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f33])).
% 3.64/0.98  
% 3.64/0.98  fof(f4,axiom,(
% 3.64/0.98    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f41,plain,(
% 3.64/0.98    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f4])).
% 3.64/0.98  
% 3.64/0.98  fof(f63,plain,(
% 3.64/0.98    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 3.64/0.98    inference(definition_unfolding,[],[f41,f62])).
% 3.64/0.98  
% 3.64/0.98  fof(f10,axiom,(
% 3.64/0.98    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f22,plain,(
% 3.64/0.98    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.64/0.98    inference(ennf_transformation,[],[f10])).
% 3.64/0.98  
% 3.64/0.98  fof(f47,plain,(
% 3.64/0.98    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f22])).
% 3.64/0.98  
% 3.64/0.98  fof(f2,axiom,(
% 3.64/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f21,plain,(
% 3.64/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.64/0.98    inference(ennf_transformation,[],[f2])).
% 3.64/0.98  
% 3.64/0.98  fof(f37,plain,(
% 3.64/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f21])).
% 3.64/0.98  
% 3.64/0.98  fof(f17,axiom,(
% 3.64/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f29,plain,(
% 3.64/0.98    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.64/0.98    inference(ennf_transformation,[],[f17])).
% 3.64/0.98  
% 3.64/0.98  fof(f30,plain,(
% 3.64/0.98    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.64/0.98    inference(flattening,[],[f29])).
% 3.64/0.98  
% 3.64/0.98  fof(f54,plain,(
% 3.64/0.98    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f30])).
% 3.64/0.98  
% 3.64/0.98  fof(f55,plain,(
% 3.64/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.64/0.98    inference(cnf_transformation,[],[f18])).
% 3.64/0.98  
% 3.64/0.98  fof(f11,axiom,(
% 3.64/0.98    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.64/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.64/0.98  
% 3.64/0.98  fof(f23,plain,(
% 3.64/0.98    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.64/0.98    inference(ennf_transformation,[],[f11])).
% 3.64/0.98  
% 3.64/0.98  fof(f48,plain,(
% 3.64/0.98    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.64/0.98    inference(cnf_transformation,[],[f23])).
% 3.64/0.98  
% 3.64/0.98  fof(f58,plain,(
% 3.64/0.98    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 3.64/0.98    inference(cnf_transformation,[],[f35])).
% 3.64/0.98  
% 3.64/0.98  cnf(c_17,negated_conjecture,
% 3.64/0.98      ( v1_relat_1(sK0) ),
% 3.64/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_442,plain,
% 3.64/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_0,plain,
% 3.64/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.64/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_454,plain,
% 3.64/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9,plain,
% 3.64/0.98      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.64/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_447,plain,
% 3.64/0.98      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_923,plain,
% 3.64/0.98      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_454,c_447]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_10,plain,
% 3.64/0.98      ( ~ v1_relat_1(X0)
% 3.64/0.98      | ~ v1_relat_1(X1)
% 3.64/0.98      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.64/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_446,plain,
% 3.64/0.98      ( v1_relat_1(X0) != iProver_top
% 3.64/0.98      | v1_relat_1(X1) != iProver_top
% 3.64/0.98      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_11,plain,
% 3.64/0.98      ( ~ v1_relat_1(X0)
% 3.64/0.98      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 3.64/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_445,plain,
% 3.64/0.98      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1261,plain,
% 3.64/0.98      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 3.64/0.98      | v1_relat_1(X1) != iProver_top
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_446,c_445]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3024,plain,
% 3.64/0.98      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k5_relat_1(X0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,k1_xboole_0)),k2_relat_1(k5_relat_1(X0,k1_xboole_0))))) = k5_relat_1(X0,k1_xboole_0)
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_923,c_1261]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9896,plain,
% 3.64/0.98      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_442,c_3024]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_14,plain,
% 3.64/0.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_12,plain,
% 3.64/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.64/0.98      | ~ v1_relat_1(X1)
% 3.64/0.98      | ~ v1_relat_1(X0) ),
% 3.64/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_444,plain,
% 3.64/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.64/0.98      | v1_relat_1(X1) != iProver_top
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_916,plain,
% 3.64/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 3.64/0.98      | v1_relat_1(X0) != iProver_top
% 3.64/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_14,c_444]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_31,plain,
% 3.64/0.98      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_33,plain,
% 3.64/0.98      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.64/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.64/0.98      inference(instantiation,[status(thm)],[c_31]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_50,plain,
% 3.64/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1266,plain,
% 3.64/0.98      ( v1_relat_1(X0) != iProver_top
% 3.64/0.98      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 3.64/0.98      inference(global_propositional_subsumption,
% 3.64/0.98                [status(thm)],
% 3.64/0.98                [c_916,c_33,c_50]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1267,plain,
% 3.64/0.98      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(renaming,[status(thm)],[c_1266]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_6,plain,
% 3.64/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.64/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_450,plain,
% 3.64/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_2,plain,
% 3.64/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.64/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_452,plain,
% 3.64/0.98      ( X0 = X1
% 3.64/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.64/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1145,plain,
% 3.64/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_450,c_452]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1700,plain,
% 3.64/0.98      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_1267,c_1145]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_6589,plain,
% 3.64/0.98      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_442,c_1700]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9913,plain,
% 3.64/0.98      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.64/0.98      inference(light_normalisation,[status(thm)],[c_9896,c_6589]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_5,plain,
% 3.64/0.98      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.64/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_7,plain,
% 3.64/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.64/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_449,plain,
% 3.64/0.98      ( v1_xboole_0(X0) != iProver_top
% 3.64/0.98      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1,plain,
% 3.64/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.64/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_453,plain,
% 3.64/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1043,plain,
% 3.64/0.98      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.64/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_449,c_453]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_2038,plain,
% 3.64/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_454,c_1043]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9914,plain,
% 3.64/0.98      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.98      inference(demodulation,[status(thm)],[c_9913,c_5,c_2038]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_3023,plain,
% 3.64/0.98      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) = k5_relat_1(X0,sK0)
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_442,c_1261]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9524,plain,
% 3.64/0.98      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_923,c_3023]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_13,plain,
% 3.64/0.98      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.64/0.98      | ~ v1_relat_1(X1)
% 3.64/0.98      | ~ v1_relat_1(X0)
% 3.64/0.98      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.64/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_443,plain,
% 3.64/0.98      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 3.64/0.98      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.64/0.98      | v1_relat_1(X1) != iProver_top
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_610,plain,
% 3.64/0.98      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 3.64/0.98      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.64/0.98      | v1_relat_1(X0) != iProver_top
% 3.64/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_14,c_443]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_15,plain,
% 3.64/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.64/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_624,plain,
% 3.64/0.98      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.64/0.98      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.64/0.98      | v1_relat_1(X0) != iProver_top
% 3.64/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.64/0.98      inference(light_normalisation,[status(thm)],[c_610,c_15]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1444,plain,
% 3.64/0.98      ( v1_relat_1(X0) != iProver_top
% 3.64/0.98      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.64/0.98      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.64/0.98      inference(global_propositional_subsumption,
% 3.64/0.98                [status(thm)],
% 3.64/0.98                [c_624,c_33,c_50]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1445,plain,
% 3.64/0.98      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.64/0.98      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(renaming,[status(thm)],[c_1444]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1451,plain,
% 3.64/0.98      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.64/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.64/0.98      inference(forward_subsumption_resolution,
% 3.64/0.98                [status(thm)],
% 3.64/0.98                [c_1445,c_450]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1456,plain,
% 3.64/0.98      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_442,c_1451]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9536,plain,
% 3.64/0.98      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.64/0.98      inference(light_normalisation,[status(thm)],[c_9524,c_1456]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_8,plain,
% 3.64/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.64/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_448,plain,
% 3.64/0.98      ( v1_xboole_0(X0) != iProver_top
% 3.64/0.98      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.64/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1024,plain,
% 3.64/0.98      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.64/0.98      | v1_xboole_0(X0) != iProver_top ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_448,c_453]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_1926,plain,
% 3.64/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.64/0.98      inference(superposition,[status(thm)],[c_454,c_1024]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9537,plain,
% 3.64/0.98      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 3.64/0.98      inference(demodulation,[status(thm)],[c_9536,c_5,c_1926]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_16,negated_conjecture,
% 3.64/0.98      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 3.64/0.98      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 3.64/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9557,plain,
% 3.64/0.98      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 3.64/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.64/0.98      inference(demodulation,[status(thm)],[c_9537,c_16]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(c_9558,plain,
% 3.64/0.98      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.64/0.98      inference(equality_resolution_simp,[status(thm)],[c_9557]) ).
% 3.64/0.98  
% 3.64/0.98  cnf(contradiction,plain,
% 3.64/0.98      ( $false ),
% 3.64/0.98      inference(minisat,[status(thm)],[c_9914,c_9558]) ).
% 3.64/0.98  
% 3.64/0.98  
% 3.64/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.64/0.98  
% 3.64/0.98  ------                               Statistics
% 3.64/0.98  
% 3.64/0.98  ------ Selected
% 3.64/0.98  
% 3.64/0.98  total_time:                             0.36
% 3.64/0.98  
%------------------------------------------------------------------------------
