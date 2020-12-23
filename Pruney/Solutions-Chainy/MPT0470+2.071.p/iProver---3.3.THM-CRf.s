%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:07 EST 2020

% Result     : Theorem 7.18s
% Output     : CNFRefutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 489 expanded)
%              Number of clauses        :   97 ( 217 expanded)
%              Number of leaves         :   25 (  98 expanded)
%              Depth                    :   25
%              Number of atoms          :  348 (1030 expanded)
%              Number of equality atoms :  221 ( 510 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f36,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f39])).

fof(f65,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f68])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f69])).

fof(f72,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f64,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f66,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_554,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_553,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_546,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_557,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_555,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_848,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_555])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_547,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1259,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_547])).

cnf(c_4011,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_1259])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_549,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1286,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_848,c_549])).

cnf(c_18,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1288,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1286,c_18])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_552,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1415,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_552])).

cnf(c_46,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_48,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_49,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_51,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_61,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6209,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1415,c_48,c_51,c_61])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_556,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6215,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6209,c_556])).

cnf(c_12404,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4011,c_6215])).

cnf(c_12412,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_546,c_12404])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_551,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_924,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_546,c_551])).

cnf(c_12473,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_12412,c_924])).

cnf(c_13170,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12473,c_554])).

cnf(c_13439,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_553,c_13170])).

cnf(c_17762,plain,
    ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13439,c_51,c_61])).

cnf(c_17763,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17762])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_550,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_17828,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0)
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17763,c_550])).

cnf(c_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_180,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X1) != X2
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_181,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_545,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_181])).

cnf(c_759,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_545])).

cnf(c_760,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_759,c_18])).

cnf(c_2015,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_51,c_61])).

cnf(c_2016,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2015])).

cnf(c_2023,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_546,c_2016])).

cnf(c_17860,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0)
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17828,c_2023])).

cnf(c_2,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_17861,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17860,c_2,c_5])).

cnf(c_18065,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_17861])).

cnf(c_21,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18748,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18065,c_21])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_18770,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18748,c_19])).

cnf(c_18771,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_18770])).

cnf(c_303,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1330,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X1))
    | k2_relat_1(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_7515,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,X1)))))
    | k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,X1)))) != X0 ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_7517,plain,
    ( v1_xboole_0(k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7515])).

cnf(c_4013,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_546,c_1259])).

cnf(c_6252,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_6215,c_4013])).

cnf(c_2021,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_2016])).

cnf(c_2202,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_546,c_2021])).

cnf(c_6455,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6252,c_2202])).

cnf(c_4056,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4013,c_553])).

cnf(c_703,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_704,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_2751,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2752,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2751])).

cnf(c_4737,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4056,c_21,c_51,c_61,c_704,c_2752])).

cnf(c_4762,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_4737,c_549])).

cnf(c_6544,plain,
    ( k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6455,c_4762])).

cnf(c_1215,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_985,plain,
    ( ~ v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))
    | ~ v1_xboole_0(k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))
    | v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_957,plain,
    ( ~ v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_302,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_689,plain,
    ( X0 != X1
    | k5_relat_1(sK0,k1_xboole_0) != X1
    | k5_relat_1(sK0,k1_xboole_0) = X0 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_899,plain,
    ( X0 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k5_relat_1(sK0,k1_xboole_0) = X0
    | k5_relat_1(sK0,k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_900,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_770,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_710,plain,
    ( X0 != k5_relat_1(sK0,k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) = X0
    | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_769,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_301,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_711,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_50,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18771,c_7517,c_6544,c_2751,c_1215,c_985,c_957,c_900,c_770,c_769,c_711,c_703,c_0,c_50,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:46:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.18/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.18/1.47  
% 7.18/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.18/1.47  
% 7.18/1.47  ------  iProver source info
% 7.18/1.47  
% 7.18/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.18/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.18/1.47  git: non_committed_changes: false
% 7.18/1.47  git: last_make_outside_of_git: false
% 7.18/1.47  
% 7.18/1.47  ------ 
% 7.18/1.47  
% 7.18/1.47  ------ Input Options
% 7.18/1.47  
% 7.18/1.47  --out_options                           all
% 7.18/1.47  --tptp_safe_out                         true
% 7.18/1.47  --problem_path                          ""
% 7.18/1.47  --include_path                          ""
% 7.18/1.47  --clausifier                            res/vclausify_rel
% 7.18/1.47  --clausifier_options                    --mode clausify
% 7.18/1.47  --stdin                                 false
% 7.18/1.47  --stats_out                             all
% 7.18/1.47  
% 7.18/1.47  ------ General Options
% 7.18/1.47  
% 7.18/1.47  --fof                                   false
% 7.18/1.47  --time_out_real                         305.
% 7.18/1.47  --time_out_virtual                      -1.
% 7.18/1.47  --symbol_type_check                     false
% 7.18/1.47  --clausify_out                          false
% 7.18/1.47  --sig_cnt_out                           false
% 7.18/1.47  --trig_cnt_out                          false
% 7.18/1.47  --trig_cnt_out_tolerance                1.
% 7.18/1.47  --trig_cnt_out_sk_spl                   false
% 7.18/1.47  --abstr_cl_out                          false
% 7.18/1.47  
% 7.18/1.47  ------ Global Options
% 7.18/1.47  
% 7.18/1.47  --schedule                              default
% 7.18/1.47  --add_important_lit                     false
% 7.18/1.47  --prop_solver_per_cl                    1000
% 7.18/1.47  --min_unsat_core                        false
% 7.18/1.47  --soft_assumptions                      false
% 7.18/1.47  --soft_lemma_size                       3
% 7.18/1.47  --prop_impl_unit_size                   0
% 7.18/1.47  --prop_impl_unit                        []
% 7.18/1.47  --share_sel_clauses                     true
% 7.18/1.47  --reset_solvers                         false
% 7.18/1.47  --bc_imp_inh                            [conj_cone]
% 7.18/1.47  --conj_cone_tolerance                   3.
% 7.18/1.47  --extra_neg_conj                        none
% 7.18/1.47  --large_theory_mode                     true
% 7.18/1.47  --prolific_symb_bound                   200
% 7.18/1.47  --lt_threshold                          2000
% 7.18/1.47  --clause_weak_htbl                      true
% 7.18/1.47  --gc_record_bc_elim                     false
% 7.18/1.48  
% 7.18/1.48  ------ Preprocessing Options
% 7.18/1.48  
% 7.18/1.48  --preprocessing_flag                    true
% 7.18/1.48  --time_out_prep_mult                    0.1
% 7.18/1.48  --splitting_mode                        input
% 7.18/1.48  --splitting_grd                         true
% 7.18/1.48  --splitting_cvd                         false
% 7.18/1.48  --splitting_cvd_svl                     false
% 7.18/1.48  --splitting_nvd                         32
% 7.18/1.48  --sub_typing                            true
% 7.18/1.48  --prep_gs_sim                           true
% 7.18/1.48  --prep_unflatten                        true
% 7.18/1.48  --prep_res_sim                          true
% 7.18/1.48  --prep_upred                            true
% 7.18/1.48  --prep_sem_filter                       exhaustive
% 7.18/1.48  --prep_sem_filter_out                   false
% 7.18/1.48  --pred_elim                             true
% 7.18/1.48  --res_sim_input                         true
% 7.18/1.48  --eq_ax_congr_red                       true
% 7.18/1.48  --pure_diseq_elim                       true
% 7.18/1.48  --brand_transform                       false
% 7.18/1.48  --non_eq_to_eq                          false
% 7.18/1.48  --prep_def_merge                        true
% 7.18/1.48  --prep_def_merge_prop_impl              false
% 7.18/1.48  --prep_def_merge_mbd                    true
% 7.18/1.48  --prep_def_merge_tr_red                 false
% 7.18/1.48  --prep_def_merge_tr_cl                  false
% 7.18/1.48  --smt_preprocessing                     true
% 7.18/1.48  --smt_ac_axioms                         fast
% 7.18/1.48  --preprocessed_out                      false
% 7.18/1.48  --preprocessed_stats                    false
% 7.18/1.48  
% 7.18/1.48  ------ Abstraction refinement Options
% 7.18/1.48  
% 7.18/1.48  --abstr_ref                             []
% 7.18/1.48  --abstr_ref_prep                        false
% 7.18/1.48  --abstr_ref_until_sat                   false
% 7.18/1.48  --abstr_ref_sig_restrict                funpre
% 7.18/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.18/1.48  --abstr_ref_under                       []
% 7.18/1.48  
% 7.18/1.48  ------ SAT Options
% 7.18/1.48  
% 7.18/1.48  --sat_mode                              false
% 7.18/1.48  --sat_fm_restart_options                ""
% 7.18/1.48  --sat_gr_def                            false
% 7.18/1.48  --sat_epr_types                         true
% 7.18/1.48  --sat_non_cyclic_types                  false
% 7.18/1.48  --sat_finite_models                     false
% 7.18/1.48  --sat_fm_lemmas                         false
% 7.18/1.48  --sat_fm_prep                           false
% 7.18/1.48  --sat_fm_uc_incr                        true
% 7.18/1.48  --sat_out_model                         small
% 7.18/1.48  --sat_out_clauses                       false
% 7.18/1.48  
% 7.18/1.48  ------ QBF Options
% 7.18/1.48  
% 7.18/1.48  --qbf_mode                              false
% 7.18/1.48  --qbf_elim_univ                         false
% 7.18/1.48  --qbf_dom_inst                          none
% 7.18/1.48  --qbf_dom_pre_inst                      false
% 7.18/1.48  --qbf_sk_in                             false
% 7.18/1.48  --qbf_pred_elim                         true
% 7.18/1.48  --qbf_split                             512
% 7.18/1.48  
% 7.18/1.48  ------ BMC1 Options
% 7.18/1.48  
% 7.18/1.48  --bmc1_incremental                      false
% 7.18/1.48  --bmc1_axioms                           reachable_all
% 7.18/1.48  --bmc1_min_bound                        0
% 7.18/1.48  --bmc1_max_bound                        -1
% 7.18/1.48  --bmc1_max_bound_default                -1
% 7.18/1.48  --bmc1_symbol_reachability              true
% 7.18/1.48  --bmc1_property_lemmas                  false
% 7.18/1.48  --bmc1_k_induction                      false
% 7.18/1.48  --bmc1_non_equiv_states                 false
% 7.18/1.48  --bmc1_deadlock                         false
% 7.18/1.48  --bmc1_ucm                              false
% 7.18/1.48  --bmc1_add_unsat_core                   none
% 7.18/1.48  --bmc1_unsat_core_children              false
% 7.18/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.18/1.48  --bmc1_out_stat                         full
% 7.18/1.48  --bmc1_ground_init                      false
% 7.18/1.48  --bmc1_pre_inst_next_state              false
% 7.18/1.48  --bmc1_pre_inst_state                   false
% 7.18/1.48  --bmc1_pre_inst_reach_state             false
% 7.18/1.48  --bmc1_out_unsat_core                   false
% 7.18/1.48  --bmc1_aig_witness_out                  false
% 7.18/1.48  --bmc1_verbose                          false
% 7.18/1.48  --bmc1_dump_clauses_tptp                false
% 7.18/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.18/1.48  --bmc1_dump_file                        -
% 7.18/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.18/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.18/1.48  --bmc1_ucm_extend_mode                  1
% 7.18/1.48  --bmc1_ucm_init_mode                    2
% 7.18/1.48  --bmc1_ucm_cone_mode                    none
% 7.18/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.18/1.48  --bmc1_ucm_relax_model                  4
% 7.18/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.18/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.18/1.48  --bmc1_ucm_layered_model                none
% 7.18/1.48  --bmc1_ucm_max_lemma_size               10
% 7.18/1.48  
% 7.18/1.48  ------ AIG Options
% 7.18/1.48  
% 7.18/1.48  --aig_mode                              false
% 7.18/1.48  
% 7.18/1.48  ------ Instantiation Options
% 7.18/1.48  
% 7.18/1.48  --instantiation_flag                    true
% 7.18/1.48  --inst_sos_flag                         false
% 7.18/1.48  --inst_sos_phase                        true
% 7.18/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.18/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.18/1.48  --inst_lit_sel_side                     num_symb
% 7.18/1.48  --inst_solver_per_active                1400
% 7.18/1.48  --inst_solver_calls_frac                1.
% 7.18/1.48  --inst_passive_queue_type               priority_queues
% 7.18/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.18/1.48  --inst_passive_queues_freq              [25;2]
% 7.18/1.48  --inst_dismatching                      true
% 7.18/1.48  --inst_eager_unprocessed_to_passive     true
% 7.18/1.48  --inst_prop_sim_given                   true
% 7.18/1.48  --inst_prop_sim_new                     false
% 7.18/1.48  --inst_subs_new                         false
% 7.18/1.48  --inst_eq_res_simp                      false
% 7.18/1.48  --inst_subs_given                       false
% 7.18/1.48  --inst_orphan_elimination               true
% 7.18/1.48  --inst_learning_loop_flag               true
% 7.18/1.48  --inst_learning_start                   3000
% 7.18/1.48  --inst_learning_factor                  2
% 7.18/1.48  --inst_start_prop_sim_after_learn       3
% 7.18/1.48  --inst_sel_renew                        solver
% 7.18/1.48  --inst_lit_activity_flag                true
% 7.18/1.48  --inst_restr_to_given                   false
% 7.18/1.48  --inst_activity_threshold               500
% 7.18/1.48  --inst_out_proof                        true
% 7.18/1.48  
% 7.18/1.48  ------ Resolution Options
% 7.18/1.48  
% 7.18/1.48  --resolution_flag                       true
% 7.18/1.48  --res_lit_sel                           adaptive
% 7.18/1.48  --res_lit_sel_side                      none
% 7.18/1.48  --res_ordering                          kbo
% 7.18/1.48  --res_to_prop_solver                    active
% 7.18/1.48  --res_prop_simpl_new                    false
% 7.18/1.48  --res_prop_simpl_given                  true
% 7.18/1.48  --res_passive_queue_type                priority_queues
% 7.18/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.18/1.48  --res_passive_queues_freq               [15;5]
% 7.18/1.48  --res_forward_subs                      full
% 7.18/1.48  --res_backward_subs                     full
% 7.18/1.48  --res_forward_subs_resolution           true
% 7.18/1.48  --res_backward_subs_resolution          true
% 7.18/1.48  --res_orphan_elimination                true
% 7.18/1.48  --res_time_limit                        2.
% 7.18/1.48  --res_out_proof                         true
% 7.18/1.48  
% 7.18/1.48  ------ Superposition Options
% 7.18/1.48  
% 7.18/1.48  --superposition_flag                    true
% 7.18/1.48  --sup_passive_queue_type                priority_queues
% 7.18/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.18/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.18/1.48  --demod_completeness_check              fast
% 7.18/1.48  --demod_use_ground                      true
% 7.18/1.48  --sup_to_prop_solver                    passive
% 7.18/1.48  --sup_prop_simpl_new                    true
% 7.18/1.48  --sup_prop_simpl_given                  true
% 7.18/1.48  --sup_fun_splitting                     false
% 7.18/1.48  --sup_smt_interval                      50000
% 7.18/1.48  
% 7.18/1.48  ------ Superposition Simplification Setup
% 7.18/1.48  
% 7.18/1.48  --sup_indices_passive                   []
% 7.18/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.18/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.18/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.18/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.18/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.18/1.48  --sup_full_bw                           [BwDemod]
% 7.18/1.48  --sup_immed_triv                        [TrivRules]
% 7.18/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.18/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.18/1.48  --sup_immed_bw_main                     []
% 7.18/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.18/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.18/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.18/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.18/1.48  
% 7.18/1.48  ------ Combination Options
% 7.18/1.48  
% 7.18/1.48  --comb_res_mult                         3
% 7.18/1.48  --comb_sup_mult                         2
% 7.18/1.48  --comb_inst_mult                        10
% 7.18/1.48  
% 7.18/1.48  ------ Debug Options
% 7.18/1.48  
% 7.18/1.48  --dbg_backtrace                         false
% 7.18/1.48  --dbg_dump_prop_clauses                 false
% 7.18/1.48  --dbg_dump_prop_clauses_file            -
% 7.18/1.48  --dbg_out_stat                          false
% 7.18/1.48  ------ Parsing...
% 7.18/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.18/1.48  
% 7.18/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.18/1.48  
% 7.18/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.18/1.48  
% 7.18/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.18/1.48  ------ Proving...
% 7.18/1.48  ------ Problem Properties 
% 7.18/1.48  
% 7.18/1.48  
% 7.18/1.48  clauses                                 20
% 7.18/1.48  conjectures                             2
% 7.18/1.48  EPR                                     4
% 7.18/1.48  Horn                                    19
% 7.18/1.48  unary                                   7
% 7.18/1.48  binary                                  8
% 7.18/1.48  lits                                    39
% 7.18/1.48  lits eq                                 18
% 7.18/1.48  fd_pure                                 0
% 7.18/1.48  fd_pseudo                               0
% 7.18/1.48  fd_cond                                 2
% 7.18/1.48  fd_pseudo_cond                          0
% 7.18/1.48  AC symbols                              0
% 7.18/1.48  
% 7.18/1.48  ------ Schedule dynamic 5 is on 
% 7.18/1.48  
% 7.18/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.18/1.48  
% 7.18/1.48  
% 7.18/1.48  ------ 
% 7.18/1.48  Current options:
% 7.18/1.48  ------ 
% 7.18/1.48  
% 7.18/1.48  ------ Input Options
% 7.18/1.48  
% 7.18/1.48  --out_options                           all
% 7.18/1.48  --tptp_safe_out                         true
% 7.18/1.48  --problem_path                          ""
% 7.18/1.48  --include_path                          ""
% 7.18/1.48  --clausifier                            res/vclausify_rel
% 7.18/1.48  --clausifier_options                    --mode clausify
% 7.18/1.48  --stdin                                 false
% 7.18/1.48  --stats_out                             all
% 7.18/1.48  
% 7.18/1.48  ------ General Options
% 7.18/1.48  
% 7.18/1.48  --fof                                   false
% 7.18/1.48  --time_out_real                         305.
% 7.18/1.48  --time_out_virtual                      -1.
% 7.18/1.48  --symbol_type_check                     false
% 7.18/1.48  --clausify_out                          false
% 7.18/1.48  --sig_cnt_out                           false
% 7.18/1.48  --trig_cnt_out                          false
% 7.18/1.48  --trig_cnt_out_tolerance                1.
% 7.18/1.48  --trig_cnt_out_sk_spl                   false
% 7.18/1.48  --abstr_cl_out                          false
% 7.18/1.48  
% 7.18/1.48  ------ Global Options
% 7.18/1.48  
% 7.18/1.48  --schedule                              default
% 7.18/1.48  --add_important_lit                     false
% 7.18/1.48  --prop_solver_per_cl                    1000
% 7.18/1.48  --min_unsat_core                        false
% 7.18/1.48  --soft_assumptions                      false
% 7.18/1.48  --soft_lemma_size                       3
% 7.18/1.48  --prop_impl_unit_size                   0
% 7.18/1.48  --prop_impl_unit                        []
% 7.18/1.48  --share_sel_clauses                     true
% 7.18/1.48  --reset_solvers                         false
% 7.18/1.48  --bc_imp_inh                            [conj_cone]
% 7.18/1.48  --conj_cone_tolerance                   3.
% 7.18/1.48  --extra_neg_conj                        none
% 7.18/1.48  --large_theory_mode                     true
% 7.18/1.48  --prolific_symb_bound                   200
% 7.18/1.48  --lt_threshold                          2000
% 7.18/1.48  --clause_weak_htbl                      true
% 7.18/1.48  --gc_record_bc_elim                     false
% 7.18/1.48  
% 7.18/1.48  ------ Preprocessing Options
% 7.18/1.48  
% 7.18/1.48  --preprocessing_flag                    true
% 7.18/1.48  --time_out_prep_mult                    0.1
% 7.18/1.48  --splitting_mode                        input
% 7.18/1.48  --splitting_grd                         true
% 7.18/1.48  --splitting_cvd                         false
% 7.18/1.48  --splitting_cvd_svl                     false
% 7.18/1.48  --splitting_nvd                         32
% 7.18/1.48  --sub_typing                            true
% 7.18/1.48  --prep_gs_sim                           true
% 7.18/1.48  --prep_unflatten                        true
% 7.18/1.48  --prep_res_sim                          true
% 7.18/1.48  --prep_upred                            true
% 7.18/1.48  --prep_sem_filter                       exhaustive
% 7.18/1.48  --prep_sem_filter_out                   false
% 7.18/1.48  --pred_elim                             true
% 7.18/1.48  --res_sim_input                         true
% 7.18/1.48  --eq_ax_congr_red                       true
% 7.18/1.48  --pure_diseq_elim                       true
% 7.18/1.48  --brand_transform                       false
% 7.18/1.48  --non_eq_to_eq                          false
% 7.18/1.48  --prep_def_merge                        true
% 7.18/1.48  --prep_def_merge_prop_impl              false
% 7.18/1.48  --prep_def_merge_mbd                    true
% 7.18/1.48  --prep_def_merge_tr_red                 false
% 7.18/1.48  --prep_def_merge_tr_cl                  false
% 7.18/1.48  --smt_preprocessing                     true
% 7.18/1.48  --smt_ac_axioms                         fast
% 7.18/1.48  --preprocessed_out                      false
% 7.18/1.48  --preprocessed_stats                    false
% 7.18/1.48  
% 7.18/1.48  ------ Abstraction refinement Options
% 7.18/1.48  
% 7.18/1.48  --abstr_ref                             []
% 7.18/1.48  --abstr_ref_prep                        false
% 7.18/1.48  --abstr_ref_until_sat                   false
% 7.18/1.48  --abstr_ref_sig_restrict                funpre
% 7.18/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.18/1.48  --abstr_ref_under                       []
% 7.18/1.48  
% 7.18/1.48  ------ SAT Options
% 7.18/1.48  
% 7.18/1.48  --sat_mode                              false
% 7.18/1.48  --sat_fm_restart_options                ""
% 7.18/1.48  --sat_gr_def                            false
% 7.18/1.48  --sat_epr_types                         true
% 7.18/1.48  --sat_non_cyclic_types                  false
% 7.18/1.48  --sat_finite_models                     false
% 7.18/1.48  --sat_fm_lemmas                         false
% 7.18/1.48  --sat_fm_prep                           false
% 7.18/1.48  --sat_fm_uc_incr                        true
% 7.18/1.48  --sat_out_model                         small
% 7.18/1.48  --sat_out_clauses                       false
% 7.18/1.48  
% 7.18/1.48  ------ QBF Options
% 7.18/1.48  
% 7.18/1.48  --qbf_mode                              false
% 7.18/1.48  --qbf_elim_univ                         false
% 7.18/1.48  --qbf_dom_inst                          none
% 7.18/1.48  --qbf_dom_pre_inst                      false
% 7.18/1.48  --qbf_sk_in                             false
% 7.18/1.48  --qbf_pred_elim                         true
% 7.18/1.48  --qbf_split                             512
% 7.18/1.48  
% 7.18/1.48  ------ BMC1 Options
% 7.18/1.48  
% 7.18/1.48  --bmc1_incremental                      false
% 7.18/1.48  --bmc1_axioms                           reachable_all
% 7.18/1.48  --bmc1_min_bound                        0
% 7.18/1.48  --bmc1_max_bound                        -1
% 7.18/1.48  --bmc1_max_bound_default                -1
% 7.18/1.48  --bmc1_symbol_reachability              true
% 7.18/1.48  --bmc1_property_lemmas                  false
% 7.18/1.48  --bmc1_k_induction                      false
% 7.18/1.48  --bmc1_non_equiv_states                 false
% 7.18/1.48  --bmc1_deadlock                         false
% 7.18/1.48  --bmc1_ucm                              false
% 7.18/1.48  --bmc1_add_unsat_core                   none
% 7.18/1.48  --bmc1_unsat_core_children              false
% 7.18/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.18/1.48  --bmc1_out_stat                         full
% 7.18/1.48  --bmc1_ground_init                      false
% 7.18/1.48  --bmc1_pre_inst_next_state              false
% 7.18/1.48  --bmc1_pre_inst_state                   false
% 7.18/1.48  --bmc1_pre_inst_reach_state             false
% 7.18/1.48  --bmc1_out_unsat_core                   false
% 7.18/1.48  --bmc1_aig_witness_out                  false
% 7.18/1.48  --bmc1_verbose                          false
% 7.18/1.48  --bmc1_dump_clauses_tptp                false
% 7.18/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.18/1.48  --bmc1_dump_file                        -
% 7.18/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.18/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.18/1.48  --bmc1_ucm_extend_mode                  1
% 7.18/1.48  --bmc1_ucm_init_mode                    2
% 7.18/1.48  --bmc1_ucm_cone_mode                    none
% 7.18/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.18/1.48  --bmc1_ucm_relax_model                  4
% 7.18/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.18/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.18/1.48  --bmc1_ucm_layered_model                none
% 7.18/1.48  --bmc1_ucm_max_lemma_size               10
% 7.18/1.48  
% 7.18/1.48  ------ AIG Options
% 7.18/1.48  
% 7.18/1.48  --aig_mode                              false
% 7.18/1.48  
% 7.18/1.48  ------ Instantiation Options
% 7.18/1.48  
% 7.18/1.48  --instantiation_flag                    true
% 7.18/1.48  --inst_sos_flag                         false
% 7.18/1.48  --inst_sos_phase                        true
% 7.18/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.18/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.18/1.48  --inst_lit_sel_side                     none
% 7.18/1.48  --inst_solver_per_active                1400
% 7.18/1.48  --inst_solver_calls_frac                1.
% 7.18/1.48  --inst_passive_queue_type               priority_queues
% 7.18/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.18/1.48  --inst_passive_queues_freq              [25;2]
% 7.18/1.48  --inst_dismatching                      true
% 7.18/1.48  --inst_eager_unprocessed_to_passive     true
% 7.18/1.48  --inst_prop_sim_given                   true
% 7.18/1.48  --inst_prop_sim_new                     false
% 7.18/1.48  --inst_subs_new                         false
% 7.18/1.48  --inst_eq_res_simp                      false
% 7.18/1.48  --inst_subs_given                       false
% 7.18/1.48  --inst_orphan_elimination               true
% 7.18/1.48  --inst_learning_loop_flag               true
% 7.18/1.48  --inst_learning_start                   3000
% 7.18/1.48  --inst_learning_factor                  2
% 7.18/1.48  --inst_start_prop_sim_after_learn       3
% 7.18/1.48  --inst_sel_renew                        solver
% 7.18/1.48  --inst_lit_activity_flag                true
% 7.18/1.48  --inst_restr_to_given                   false
% 7.18/1.48  --inst_activity_threshold               500
% 7.18/1.48  --inst_out_proof                        true
% 7.18/1.48  
% 7.18/1.48  ------ Resolution Options
% 7.18/1.48  
% 7.18/1.48  --resolution_flag                       false
% 7.18/1.48  --res_lit_sel                           adaptive
% 7.18/1.48  --res_lit_sel_side                      none
% 7.18/1.48  --res_ordering                          kbo
% 7.18/1.48  --res_to_prop_solver                    active
% 7.18/1.48  --res_prop_simpl_new                    false
% 7.18/1.48  --res_prop_simpl_given                  true
% 7.18/1.48  --res_passive_queue_type                priority_queues
% 7.18/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.18/1.48  --res_passive_queues_freq               [15;5]
% 7.18/1.48  --res_forward_subs                      full
% 7.18/1.48  --res_backward_subs                     full
% 7.18/1.48  --res_forward_subs_resolution           true
% 7.18/1.48  --res_backward_subs_resolution          true
% 7.18/1.48  --res_orphan_elimination                true
% 7.18/1.48  --res_time_limit                        2.
% 7.18/1.48  --res_out_proof                         true
% 7.18/1.48  
% 7.18/1.48  ------ Superposition Options
% 7.18/1.48  
% 7.18/1.48  --superposition_flag                    true
% 7.18/1.48  --sup_passive_queue_type                priority_queues
% 7.18/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.18/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.18/1.48  --demod_completeness_check              fast
% 7.18/1.48  --demod_use_ground                      true
% 7.18/1.48  --sup_to_prop_solver                    passive
% 7.18/1.48  --sup_prop_simpl_new                    true
% 7.18/1.48  --sup_prop_simpl_given                  true
% 7.18/1.48  --sup_fun_splitting                     false
% 7.18/1.48  --sup_smt_interval                      50000
% 7.18/1.48  
% 7.18/1.48  ------ Superposition Simplification Setup
% 7.18/1.48  
% 7.18/1.48  --sup_indices_passive                   []
% 7.18/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.18/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.18/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.18/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.18/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.18/1.48  --sup_full_bw                           [BwDemod]
% 7.18/1.48  --sup_immed_triv                        [TrivRules]
% 7.18/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.18/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.18/1.48  --sup_immed_bw_main                     []
% 7.18/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.18/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.18/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.18/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.18/1.48  
% 7.18/1.48  ------ Combination Options
% 7.18/1.48  
% 7.18/1.48  --comb_res_mult                         3
% 7.18/1.48  --comb_sup_mult                         2
% 7.18/1.48  --comb_inst_mult                        10
% 7.18/1.48  
% 7.18/1.48  ------ Debug Options
% 7.18/1.48  
% 7.18/1.48  --dbg_backtrace                         false
% 7.18/1.48  --dbg_dump_prop_clauses                 false
% 7.18/1.48  --dbg_dump_prop_clauses_file            -
% 7.18/1.48  --dbg_out_stat                          false
% 7.18/1.48  
% 7.18/1.48  
% 7.18/1.48  
% 7.18/1.48  
% 7.18/1.48  ------ Proving...
% 7.18/1.48  
% 7.18/1.48  
% 7.18/1.48  % SZS status Theorem for theBenchmark.p
% 7.18/1.48  
% 7.18/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.18/1.48  
% 7.18/1.48  fof(f12,axiom,(
% 7.18/1.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f25,plain,(
% 7.18/1.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.18/1.48    inference(ennf_transformation,[],[f12])).
% 7.18/1.48  
% 7.18/1.48  fof(f54,plain,(
% 7.18/1.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f25])).
% 7.18/1.48  
% 7.18/1.48  fof(f13,axiom,(
% 7.18/1.48    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f26,plain,(
% 7.18/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.18/1.48    inference(ennf_transformation,[],[f13])).
% 7.18/1.48  
% 7.18/1.48  fof(f27,plain,(
% 7.18/1.48    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.18/1.48    inference(flattening,[],[f26])).
% 7.18/1.48  
% 7.18/1.48  fof(f55,plain,(
% 7.18/1.48    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f27])).
% 7.18/1.48  
% 7.18/1.48  fof(f21,conjecture,(
% 7.18/1.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f22,negated_conjecture,(
% 7.18/1.48    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 7.18/1.48    inference(negated_conjecture,[],[f21])).
% 7.18/1.48  
% 7.18/1.48  fof(f36,plain,(
% 7.18/1.48    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 7.18/1.48    inference(ennf_transformation,[],[f22])).
% 7.18/1.48  
% 7.18/1.48  fof(f39,plain,(
% 7.18/1.48    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 7.18/1.48    introduced(choice_axiom,[])).
% 7.18/1.48  
% 7.18/1.48  fof(f40,plain,(
% 7.18/1.48    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 7.18/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f39])).
% 7.18/1.48  
% 7.18/1.48  fof(f65,plain,(
% 7.18/1.48    v1_relat_1(sK0)),
% 7.18/1.48    inference(cnf_transformation,[],[f40])).
% 7.18/1.48  
% 7.18/1.48  fof(f1,axiom,(
% 7.18/1.48    v1_xboole_0(k1_xboole_0)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f41,plain,(
% 7.18/1.48    v1_xboole_0(k1_xboole_0)),
% 7.18/1.48    inference(cnf_transformation,[],[f1])).
% 7.18/1.48  
% 7.18/1.48  fof(f11,axiom,(
% 7.18/1.48    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f24,plain,(
% 7.18/1.48    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 7.18/1.48    inference(ennf_transformation,[],[f11])).
% 7.18/1.48  
% 7.18/1.48  fof(f53,plain,(
% 7.18/1.48    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f24])).
% 7.18/1.48  
% 7.18/1.48  fof(f19,axiom,(
% 7.18/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f35,plain,(
% 7.18/1.48    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.18/1.48    inference(ennf_transformation,[],[f19])).
% 7.18/1.48  
% 7.18/1.48  fof(f62,plain,(
% 7.18/1.48    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f35])).
% 7.18/1.48  
% 7.18/1.48  fof(f17,axiom,(
% 7.18/1.48    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f32,plain,(
% 7.18/1.48    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.18/1.48    inference(ennf_transformation,[],[f17])).
% 7.18/1.48  
% 7.18/1.48  fof(f60,plain,(
% 7.18/1.48    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f32])).
% 7.18/1.48  
% 7.18/1.48  fof(f20,axiom,(
% 7.18/1.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f63,plain,(
% 7.18/1.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.18/1.48    inference(cnf_transformation,[],[f20])).
% 7.18/1.48  
% 7.18/1.48  fof(f14,axiom,(
% 7.18/1.48    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f28,plain,(
% 7.18/1.48    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 7.18/1.48    inference(ennf_transformation,[],[f14])).
% 7.18/1.48  
% 7.18/1.48  fof(f29,plain,(
% 7.18/1.48    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 7.18/1.48    inference(flattening,[],[f28])).
% 7.18/1.48  
% 7.18/1.48  fof(f56,plain,(
% 7.18/1.48    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f29])).
% 7.18/1.48  
% 7.18/1.48  fof(f2,axiom,(
% 7.18/1.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f23,plain,(
% 7.18/1.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.18/1.48    inference(ennf_transformation,[],[f2])).
% 7.18/1.48  
% 7.18/1.48  fof(f42,plain,(
% 7.18/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f23])).
% 7.18/1.48  
% 7.18/1.48  fof(f15,axiom,(
% 7.18/1.48    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f30,plain,(
% 7.18/1.48    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 7.18/1.48    inference(ennf_transformation,[],[f15])).
% 7.18/1.48  
% 7.18/1.48  fof(f57,plain,(
% 7.18/1.48    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f30])).
% 7.18/1.48  
% 7.18/1.48  fof(f16,axiom,(
% 7.18/1.48    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f31,plain,(
% 7.18/1.48    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.18/1.48    inference(ennf_transformation,[],[f16])).
% 7.18/1.48  
% 7.18/1.48  fof(f58,plain,(
% 7.18/1.48    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f31])).
% 7.18/1.48  
% 7.18/1.48  fof(f10,axiom,(
% 7.18/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f52,plain,(
% 7.18/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.18/1.48    inference(cnf_transformation,[],[f10])).
% 7.18/1.48  
% 7.18/1.48  fof(f5,axiom,(
% 7.18/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f45,plain,(
% 7.18/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f5])).
% 7.18/1.48  
% 7.18/1.48  fof(f6,axiom,(
% 7.18/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f46,plain,(
% 7.18/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f6])).
% 7.18/1.48  
% 7.18/1.48  fof(f7,axiom,(
% 7.18/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f47,plain,(
% 7.18/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f7])).
% 7.18/1.48  
% 7.18/1.48  fof(f8,axiom,(
% 7.18/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f48,plain,(
% 7.18/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f8])).
% 7.18/1.48  
% 7.18/1.48  fof(f67,plain,(
% 7.18/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.18/1.48    inference(definition_unfolding,[],[f47,f48])).
% 7.18/1.48  
% 7.18/1.48  fof(f68,plain,(
% 7.18/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.18/1.48    inference(definition_unfolding,[],[f46,f67])).
% 7.18/1.48  
% 7.18/1.48  fof(f69,plain,(
% 7.18/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.18/1.48    inference(definition_unfolding,[],[f45,f68])).
% 7.18/1.48  
% 7.18/1.48  fof(f70,plain,(
% 7.18/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 7.18/1.48    inference(definition_unfolding,[],[f52,f69])).
% 7.18/1.48  
% 7.18/1.48  fof(f72,plain,(
% 7.18/1.48    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 7.18/1.48    inference(definition_unfolding,[],[f58,f70])).
% 7.18/1.48  
% 7.18/1.48  fof(f64,plain,(
% 7.18/1.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.18/1.48    inference(cnf_transformation,[],[f20])).
% 7.18/1.48  
% 7.18/1.48  fof(f4,axiom,(
% 7.18/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f44,plain,(
% 7.18/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f4])).
% 7.18/1.48  
% 7.18/1.48  fof(f18,axiom,(
% 7.18/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f33,plain,(
% 7.18/1.48    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.18/1.48    inference(ennf_transformation,[],[f18])).
% 7.18/1.48  
% 7.18/1.48  fof(f34,plain,(
% 7.18/1.48    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.18/1.48    inference(flattening,[],[f33])).
% 7.18/1.48  
% 7.18/1.48  fof(f61,plain,(
% 7.18/1.48    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f34])).
% 7.18/1.48  
% 7.18/1.48  fof(f3,axiom,(
% 7.18/1.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f43,plain,(
% 7.18/1.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.18/1.48    inference(cnf_transformation,[],[f3])).
% 7.18/1.48  
% 7.18/1.48  fof(f71,plain,(
% 7.18/1.48    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 7.18/1.48    inference(definition_unfolding,[],[f43,f70])).
% 7.18/1.48  
% 7.18/1.48  fof(f9,axiom,(
% 7.18/1.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.18/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.18/1.48  
% 7.18/1.48  fof(f37,plain,(
% 7.18/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.18/1.48    inference(nnf_transformation,[],[f9])).
% 7.18/1.48  
% 7.18/1.48  fof(f38,plain,(
% 7.18/1.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.18/1.48    inference(flattening,[],[f37])).
% 7.18/1.48  
% 7.18/1.48  fof(f50,plain,(
% 7.18/1.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.18/1.48    inference(cnf_transformation,[],[f38])).
% 7.18/1.48  
% 7.18/1.48  fof(f74,plain,(
% 7.18/1.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.18/1.48    inference(equality_resolution,[],[f50])).
% 7.18/1.48  
% 7.18/1.48  fof(f66,plain,(
% 7.18/1.48    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 7.18/1.48    inference(cnf_transformation,[],[f40])).
% 7.18/1.48  
% 7.18/1.48  cnf(c_8,plain,
% 7.18/1.48      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 7.18/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_554,plain,
% 7.18/1.48      ( v1_relat_1(X0) != iProver_top
% 7.18/1.48      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_9,plain,
% 7.18/1.48      ( ~ v1_relat_1(X0)
% 7.18/1.48      | ~ v1_relat_1(X1)
% 7.18/1.48      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 7.18/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_553,plain,
% 7.18/1.48      ( v1_relat_1(X0) != iProver_top
% 7.18/1.48      | v1_relat_1(X1) != iProver_top
% 7.18/1.48      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_20,negated_conjecture,
% 7.18/1.48      ( v1_relat_1(sK0) ),
% 7.18/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_546,plain,
% 7.18/1.48      ( v1_relat_1(sK0) = iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_0,plain,
% 7.18/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 7.18/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_557,plain,
% 7.18/1.48      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_7,plain,
% 7.18/1.48      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 7.18/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_555,plain,
% 7.18/1.48      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_848,plain,
% 7.18/1.48      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_557,c_555]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_16,plain,
% 7.18/1.48      ( ~ v1_relat_1(X0)
% 7.18/1.48      | ~ v1_relat_1(X1)
% 7.18/1.48      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 7.18/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_547,plain,
% 7.18/1.48      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 7.18/1.48      | v1_relat_1(X1) != iProver_top
% 7.18/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_1259,plain,
% 7.18/1.48      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 7.18/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_848,c_547]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_4011,plain,
% 7.18/1.48      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
% 7.18/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_554,c_1259]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_13,plain,
% 7.18/1.48      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 7.18/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_549,plain,
% 7.18/1.48      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 7.18/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_1286,plain,
% 7.18/1.48      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_848,c_549]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_18,plain,
% 7.18/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.18/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_1288,plain,
% 7.18/1.48      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 7.18/1.48      inference(light_normalisation,[status(thm)],[c_1286,c_18]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_10,plain,
% 7.18/1.48      ( ~ v1_relat_1(X0)
% 7.18/1.48      | v1_xboole_0(X0)
% 7.18/1.48      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 7.18/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_552,plain,
% 7.18/1.48      ( v1_relat_1(X0) != iProver_top
% 7.18/1.48      | v1_xboole_0(X0) = iProver_top
% 7.18/1.48      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_1415,plain,
% 7.18/1.48      ( v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top
% 7.18/1.48      | v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top
% 7.18/1.48      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_1288,c_552]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_46,plain,
% 7.18/1.48      ( v1_relat_1(X0) != iProver_top
% 7.18/1.48      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_48,plain,
% 7.18/1.48      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 7.18/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_46]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_49,plain,
% 7.18/1.48      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_51,plain,
% 7.18/1.48      ( v1_relat_1(k1_xboole_0) = iProver_top
% 7.18/1.48      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_49]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_61,plain,
% 7.18/1.48      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_6209,plain,
% 7.18/1.48      ( v1_xboole_0(k4_relat_1(k1_xboole_0)) = iProver_top ),
% 7.18/1.48      inference(global_propositional_subsumption,
% 7.18/1.48                [status(thm)],
% 7.18/1.48                [c_1415,c_48,c_51,c_61]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_1,plain,
% 7.18/1.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.18/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_556,plain,
% 7.18/1.48      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_6215,plain,
% 7.18/1.48      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_6209,c_556]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_12404,plain,
% 7.18/1.48      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
% 7.18/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.18/1.48      inference(light_normalisation,[status(thm)],[c_4011,c_6215]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_12412,plain,
% 7.18/1.48      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_546,c_12404]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_11,plain,
% 7.18/1.48      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 7.18/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_551,plain,
% 7.18/1.48      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_924,plain,
% 7.18/1.48      ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_546,c_551]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_12473,plain,
% 7.18/1.48      ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,sK0) ),
% 7.18/1.48      inference(light_normalisation,[status(thm)],[c_12412,c_924]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_13170,plain,
% 7.18/1.48      ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
% 7.18/1.48      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_12473,c_554]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_13439,plain,
% 7.18/1.48      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 7.18/1.48      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 7.18/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_553,c_13170]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_17762,plain,
% 7.18/1.48      ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 7.18/1.48      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 7.18/1.48      inference(global_propositional_subsumption,
% 7.18/1.48                [status(thm)],
% 7.18/1.48                [c_13439,c_51,c_61]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_17763,plain,
% 7.18/1.48      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 7.18/1.48      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.18/1.48      inference(renaming,[status(thm)],[c_17762]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_12,plain,
% 7.18/1.48      ( ~ v1_relat_1(X0)
% 7.18/1.48      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 7.18/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_550,plain,
% 7.18/1.48      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 7.18/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_17828,plain,
% 7.18/1.48      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0)
% 7.18/1.48      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_17763,c_550]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_17,plain,
% 7.18/1.48      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.18/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_3,plain,
% 7.18/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.18/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_15,plain,
% 7.18/1.48      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 7.18/1.48      | ~ v1_relat_1(X0)
% 7.18/1.48      | ~ v1_relat_1(X1)
% 7.18/1.48      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 7.18/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_180,plain,
% 7.18/1.48      ( ~ v1_relat_1(X0)
% 7.18/1.48      | ~ v1_relat_1(X1)
% 7.18/1.48      | k1_relat_1(X1) != X2
% 7.18/1.48      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 7.18/1.48      | k2_relat_1(X0) != k1_xboole_0 ),
% 7.18/1.48      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_181,plain,
% 7.18/1.48      ( ~ v1_relat_1(X0)
% 7.18/1.48      | ~ v1_relat_1(X1)
% 7.18/1.48      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 7.18/1.48      | k2_relat_1(X0) != k1_xboole_0 ),
% 7.18/1.48      inference(unflattening,[status(thm)],[c_180]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_545,plain,
% 7.18/1.48      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 7.18/1.48      | k2_relat_1(X0) != k1_xboole_0
% 7.18/1.48      | v1_relat_1(X0) != iProver_top
% 7.18/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_181]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_759,plain,
% 7.18/1.48      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 7.18/1.48      | v1_relat_1(X0) != iProver_top
% 7.18/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_17,c_545]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_760,plain,
% 7.18/1.48      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 7.18/1.48      | v1_relat_1(X0) != iProver_top
% 7.18/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.18/1.48      inference(light_normalisation,[status(thm)],[c_759,c_18]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_2015,plain,
% 7.18/1.48      ( v1_relat_1(X0) != iProver_top
% 7.18/1.48      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.18/1.48      inference(global_propositional_subsumption,
% 7.18/1.48                [status(thm)],
% 7.18/1.48                [c_760,c_51,c_61]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_2016,plain,
% 7.18/1.48      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 7.18/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.18/1.48      inference(renaming,[status(thm)],[c_2015]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_2023,plain,
% 7.18/1.48      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_546,c_2016]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_17860,plain,
% 7.18/1.48      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0)
% 7.18/1.48      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.18/1.48      inference(light_normalisation,[status(thm)],[c_17828,c_2023]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_2,plain,
% 7.18/1.48      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.18/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_5,plain,
% 7.18/1.48      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.18/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_17861,plain,
% 7.18/1.48      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 7.18/1.48      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.18/1.48      inference(demodulation,[status(thm)],[c_17860,c_2,c_5]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_18065,plain,
% 7.18/1.48      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 7.18/1.48      | v1_relat_1(sK0) != iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_554,c_17861]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_21,plain,
% 7.18/1.48      ( v1_relat_1(sK0) = iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_18748,plain,
% 7.18/1.48      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 7.18/1.48      inference(global_propositional_subsumption,
% 7.18/1.48                [status(thm)],
% 7.18/1.48                [c_18065,c_21]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_19,negated_conjecture,
% 7.18/1.48      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 7.18/1.48      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 7.18/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_18770,plain,
% 7.18/1.48      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 7.18/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.18/1.48      inference(demodulation,[status(thm)],[c_18748,c_19]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_18771,plain,
% 7.18/1.48      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 7.18/1.48      inference(equality_resolution_simp,[status(thm)],[c_18770]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_303,plain,
% 7.18/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.18/1.48      theory(equality) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_1330,plain,
% 7.18/1.48      ( ~ v1_xboole_0(X0)
% 7.18/1.48      | v1_xboole_0(k2_relat_1(X1))
% 7.18/1.48      | k2_relat_1(X1) != X0 ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_303]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_7515,plain,
% 7.18/1.48      ( ~ v1_xboole_0(X0)
% 7.18/1.48      | v1_xboole_0(k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,X1)))))
% 7.18/1.48      | k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,X1)))) != X0 ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_1330]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_7517,plain,
% 7.18/1.48      ( v1_xboole_0(k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))
% 7.18/1.48      | ~ v1_xboole_0(k1_xboole_0)
% 7.18/1.48      | k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != k1_xboole_0 ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_7515]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_4013,plain,
% 7.18/1.48      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_546,c_1259]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_6252,plain,
% 7.18/1.48      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 7.18/1.48      inference(demodulation,[status(thm)],[c_6215,c_4013]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_2021,plain,
% 7.18/1.48      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
% 7.18/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_554,c_2016]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_2202,plain,
% 7.18/1.48      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_546,c_2021]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_6455,plain,
% 7.18/1.48      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 7.18/1.48      inference(demodulation,[status(thm)],[c_6252,c_2202]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_4056,plain,
% 7.18/1.48      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 7.18/1.48      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 7.18/1.48      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_4013,c_553]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_703,plain,
% 7.18/1.48      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 7.18/1.48      | ~ v1_relat_1(sK0)
% 7.18/1.48      | ~ v1_relat_1(k1_xboole_0) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_9]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_704,plain,
% 7.18/1.48      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 7.18/1.48      | v1_relat_1(sK0) != iProver_top
% 7.18/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_2751,plain,
% 7.18/1.48      ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 7.18/1.48      | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_2752,plain,
% 7.18/1.48      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 7.18/1.48      | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.18/1.48      inference(predicate_to_equality,[status(thm)],[c_2751]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_4737,plain,
% 7.18/1.48      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.18/1.48      inference(global_propositional_subsumption,
% 7.18/1.48                [status(thm)],
% 7.18/1.48                [c_4056,c_21,c_51,c_61,c_704,c_2752]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_4762,plain,
% 7.18/1.48      ( k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 7.18/1.48      inference(superposition,[status(thm)],[c_4737,c_549]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_6544,plain,
% 7.18/1.48      ( k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) = k1_xboole_0 ),
% 7.18/1.48      inference(demodulation,[status(thm)],[c_6455,c_4762]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_1215,plain,
% 7.18/1.48      ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 7.18/1.48      | v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_985,plain,
% 7.18/1.48      ( ~ v1_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))
% 7.18/1.48      | ~ v1_xboole_0(k2_relat_1(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))
% 7.18/1.48      | v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_957,plain,
% 7.18/1.48      ( ~ v1_xboole_0(k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))
% 7.18/1.48      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_302,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_689,plain,
% 7.18/1.48      ( X0 != X1
% 7.18/1.48      | k5_relat_1(sK0,k1_xboole_0) != X1
% 7.18/1.48      | k5_relat_1(sK0,k1_xboole_0) = X0 ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_302]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_899,plain,
% 7.18/1.48      ( X0 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 7.18/1.48      | k5_relat_1(sK0,k1_xboole_0) = X0
% 7.18/1.48      | k5_relat_1(sK0,k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_689]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_900,plain,
% 7.18/1.48      ( k5_relat_1(sK0,k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 7.18/1.48      | k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0
% 7.18/1.48      | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_899]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_770,plain,
% 7.18/1.48      ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 7.18/1.48      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_710,plain,
% 7.18/1.48      ( X0 != k5_relat_1(sK0,k1_xboole_0)
% 7.18/1.48      | k5_relat_1(sK0,k1_xboole_0) = X0
% 7.18/1.48      | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_689]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_769,plain,
% 7.18/1.48      ( k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0)
% 7.18/1.48      | k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 7.18/1.48      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_710]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_301,plain,( X0 = X0 ),theory(equality) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_711,plain,
% 7.18/1.48      ( k5_relat_1(sK0,k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_301]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(c_50,plain,
% 7.18/1.48      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 7.18/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.18/1.48  
% 7.18/1.48  cnf(contradiction,plain,
% 7.18/1.48      ( $false ),
% 7.18/1.48      inference(minisat,
% 7.18/1.48                [status(thm)],
% 7.18/1.48                [c_18771,c_7517,c_6544,c_2751,c_1215,c_985,c_957,c_900,
% 7.18/1.48                 c_770,c_769,c_711,c_703,c_0,c_50,c_20]) ).
% 7.18/1.48  
% 7.18/1.48  
% 7.18/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.18/1.48  
% 7.18/1.48  ------                               Statistics
% 7.18/1.48  
% 7.18/1.48  ------ General
% 7.18/1.48  
% 7.18/1.48  abstr_ref_over_cycles:                  0
% 7.18/1.48  abstr_ref_under_cycles:                 0
% 7.18/1.48  gc_basic_clause_elim:                   0
% 7.18/1.48  forced_gc_time:                         0
% 7.18/1.48  parsing_time:                           0.008
% 7.18/1.48  unif_index_cands_time:                  0.
% 7.18/1.48  unif_index_add_time:                    0.
% 7.18/1.48  orderings_time:                         0.
% 7.18/1.48  out_proof_time:                         0.009
% 7.18/1.48  total_time:                             0.547
% 7.18/1.48  num_of_symbols:                         43
% 7.18/1.48  num_of_terms:                           16699
% 7.18/1.48  
% 7.18/1.48  ------ Preprocessing
% 7.18/1.48  
% 7.18/1.48  num_of_splits:                          0
% 7.18/1.48  num_of_split_atoms:                     0
% 7.18/1.48  num_of_reused_defs:                     0
% 7.18/1.48  num_eq_ax_congr_red:                    15
% 7.18/1.48  num_of_sem_filtered_clauses:            1
% 7.18/1.48  num_of_subtypes:                        0
% 7.18/1.48  monotx_restored_types:                  0
% 7.18/1.48  sat_num_of_epr_types:                   0
% 7.18/1.48  sat_num_of_non_cyclic_types:            0
% 7.18/1.48  sat_guarded_non_collapsed_types:        0
% 7.18/1.48  num_pure_diseq_elim:                    0
% 7.18/1.48  simp_replaced_by:                       0
% 7.18/1.48  res_preprocessed:                       104
% 7.18/1.48  prep_upred:                             0
% 7.18/1.48  prep_unflattend:                        1
% 7.18/1.48  smt_new_axioms:                         0
% 7.18/1.48  pred_elim_cands:                        2
% 7.18/1.48  pred_elim:                              1
% 7.18/1.48  pred_elim_cl:                           1
% 7.18/1.48  pred_elim_cycles:                       3
% 7.18/1.48  merged_defs:                            0
% 7.18/1.48  merged_defs_ncl:                        0
% 7.18/1.48  bin_hyper_res:                          0
% 7.18/1.48  prep_cycles:                            4
% 7.18/1.48  pred_elim_time:                         0.001
% 7.18/1.48  splitting_time:                         0.
% 7.18/1.48  sem_filter_time:                        0.
% 7.18/1.48  monotx_time:                            0.
% 7.18/1.48  subtype_inf_time:                       0.
% 7.18/1.48  
% 7.18/1.48  ------ Problem properties
% 7.18/1.48  
% 7.18/1.48  clauses:                                20
% 7.18/1.48  conjectures:                            2
% 7.18/1.48  epr:                                    4
% 7.18/1.48  horn:                                   19
% 7.18/1.48  ground:                                 5
% 7.18/1.48  unary:                                  7
% 7.18/1.48  binary:                                 8
% 7.18/1.48  lits:                                   39
% 7.18/1.48  lits_eq:                                18
% 7.18/1.48  fd_pure:                                0
% 7.18/1.48  fd_pseudo:                              0
% 7.18/1.48  fd_cond:                                2
% 7.18/1.48  fd_pseudo_cond:                         0
% 7.18/1.48  ac_symbols:                             0
% 7.18/1.48  
% 7.18/1.48  ------ Propositional Solver
% 7.18/1.48  
% 7.18/1.48  prop_solver_calls:                      33
% 7.18/1.48  prop_fast_solver_calls:                 863
% 7.18/1.48  smt_solver_calls:                       0
% 7.18/1.48  smt_fast_solver_calls:                  0
% 7.18/1.48  prop_num_of_clauses:                    6676
% 7.18/1.48  prop_preprocess_simplified:             13411
% 7.18/1.48  prop_fo_subsumed:                       18
% 7.18/1.48  prop_solver_time:                       0.
% 7.18/1.48  smt_solver_time:                        0.
% 7.18/1.48  smt_fast_solver_time:                   0.
% 7.18/1.48  prop_fast_solver_time:                  0.
% 7.18/1.48  prop_unsat_core_time:                   0.
% 7.18/1.48  
% 7.18/1.48  ------ QBF
% 7.18/1.48  
% 7.18/1.48  qbf_q_res:                              0
% 7.18/1.48  qbf_num_tautologies:                    0
% 7.18/1.48  qbf_prep_cycles:                        0
% 7.18/1.48  
% 7.18/1.48  ------ BMC1
% 7.18/1.48  
% 7.18/1.48  bmc1_current_bound:                     -1
% 7.18/1.48  bmc1_last_solved_bound:                 -1
% 7.18/1.48  bmc1_unsat_core_size:                   -1
% 7.18/1.48  bmc1_unsat_core_parents_size:           -1
% 7.18/1.48  bmc1_merge_next_fun:                    0
% 7.18/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.18/1.48  
% 7.18/1.48  ------ Instantiation
% 7.18/1.48  
% 7.18/1.48  inst_num_of_clauses:                    2839
% 7.18/1.48  inst_num_in_passive:                    1417
% 7.18/1.48  inst_num_in_active:                     862
% 7.18/1.48  inst_num_in_unprocessed:                560
% 7.18/1.48  inst_num_of_loops:                      1100
% 7.18/1.48  inst_num_of_learning_restarts:          0
% 7.18/1.48  inst_num_moves_active_passive:          234
% 7.18/1.48  inst_lit_activity:                      0
% 7.18/1.48  inst_lit_activity_moves:                0
% 7.18/1.48  inst_num_tautologies:                   0
% 7.18/1.48  inst_num_prop_implied:                  0
% 7.18/1.48  inst_num_existing_simplified:           0
% 7.18/1.48  inst_num_eq_res_simplified:             0
% 7.18/1.48  inst_num_child_elim:                    0
% 7.18/1.48  inst_num_of_dismatching_blockings:      926
% 7.18/1.48  inst_num_of_non_proper_insts:           2721
% 7.18/1.48  inst_num_of_duplicates:                 0
% 7.18/1.48  inst_inst_num_from_inst_to_res:         0
% 7.18/1.48  inst_dismatching_checking_time:         0.
% 7.18/1.48  
% 7.18/1.48  ------ Resolution
% 7.18/1.48  
% 7.18/1.48  res_num_of_clauses:                     0
% 7.18/1.48  res_num_in_passive:                     0
% 7.18/1.48  res_num_in_active:                      0
% 7.18/1.48  res_num_of_loops:                       108
% 7.18/1.48  res_forward_subset_subsumed:            171
% 7.18/1.48  res_backward_subset_subsumed:           0
% 7.18/1.48  res_forward_subsumed:                   0
% 7.18/1.48  res_backward_subsumed:                  0
% 7.18/1.48  res_forward_subsumption_resolution:     0
% 7.18/1.48  res_backward_subsumption_resolution:    0
% 7.18/1.48  res_clause_to_clause_subsumption:       6318
% 7.18/1.48  res_orphan_elimination:                 0
% 7.18/1.48  res_tautology_del:                      326
% 7.18/1.48  res_num_eq_res_simplified:              0
% 7.18/1.48  res_num_sel_changes:                    0
% 7.18/1.48  res_moves_from_active_to_pass:          0
% 7.18/1.48  
% 7.18/1.48  ------ Superposition
% 7.18/1.48  
% 7.18/1.48  sup_time_total:                         0.
% 7.18/1.48  sup_time_generating:                    0.
% 7.18/1.48  sup_time_sim_full:                      0.
% 7.18/1.48  sup_time_sim_immed:                     0.
% 7.18/1.48  
% 7.18/1.48  sup_num_of_clauses:                     975
% 7.18/1.48  sup_num_in_active:                      170
% 7.18/1.48  sup_num_in_passive:                     805
% 7.18/1.48  sup_num_of_loops:                       218
% 7.18/1.48  sup_fw_superposition:                   703
% 7.18/1.48  sup_bw_superposition:                   469
% 7.18/1.48  sup_immediate_simplified:               173
% 7.18/1.48  sup_given_eliminated:                   1
% 7.18/1.48  comparisons_done:                       0
% 7.18/1.48  comparisons_avoided:                    0
% 7.18/1.48  
% 7.18/1.48  ------ Simplifications
% 7.18/1.48  
% 7.18/1.48  
% 7.18/1.48  sim_fw_subset_subsumed:                 12
% 7.18/1.48  sim_bw_subset_subsumed:                 10
% 7.18/1.48  sim_fw_subsumed:                        2
% 7.18/1.48  sim_bw_subsumed:                        0
% 7.18/1.48  sim_fw_subsumption_res:                 0
% 7.18/1.48  sim_bw_subsumption_res:                 0
% 7.18/1.48  sim_tautology_del:                      9
% 7.18/1.48  sim_eq_tautology_del:                   70
% 7.18/1.48  sim_eq_res_simp:                        1
% 7.18/1.48  sim_fw_demodulated:                     2
% 7.18/1.48  sim_bw_demodulated:                     42
% 7.18/1.48  sim_light_normalised:                   167
% 7.18/1.48  sim_joinable_taut:                      0
% 7.18/1.48  sim_joinable_simp:                      0
% 7.18/1.48  sim_ac_normalised:                      0
% 7.18/1.48  sim_smt_subsumption:                    0
% 7.18/1.48  
%------------------------------------------------------------------------------
