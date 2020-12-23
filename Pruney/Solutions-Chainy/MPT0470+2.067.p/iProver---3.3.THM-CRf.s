%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:07 EST 2020

% Result     : Theorem 43.74s
% Output     : CNFRefutation 43.74s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 999 expanded)
%              Number of clauses        :   87 ( 306 expanded)
%              Number of leaves         :   25 ( 241 expanded)
%              Depth                    :   24
%              Number of atoms          :  296 (1753 expanded)
%              Number of equality atoms :  192 (1133 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f39,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f40,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f66,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f73,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f23,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_390,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_402,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_398,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1110,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_402,c_398])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_391,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1115,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_391])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_393,plain,
    ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2393,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_390,c_393])).

cnf(c_3114,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_390,c_2393])).

cnf(c_1,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_799,plain,
    ( k6_subset_1(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_804,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_799,c_5])).

cnf(c_3125,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3114,c_804])).

cnf(c_3636,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1115,c_3125])).

cnf(c_3644,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_390,c_3636])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_396,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3872,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_396])).

cnf(c_42,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_44,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_57,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4142,plain,
    ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3872,c_44,c_57])).

cnf(c_4143,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4142])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_394,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4157,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4143,c_394])).

cnf(c_4232,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4157])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9838,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_93941,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4157,c_19,c_4232,c_9838])).

cnf(c_397,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_14,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_392,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1324,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_392])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1338,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1324,c_17])).

cnf(c_2772,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1338,c_44,c_57])).

cnf(c_2773,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2772])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_400,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2779,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2773,c_400])).

cnf(c_2783,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_397,c_2779])).

cnf(c_5369,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_390,c_2783])).

cnf(c_5394,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5369,c_3644])).

cnf(c_93943,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_93941,c_5394])).

cnf(c_3,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_399,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_401,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1488,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_399,c_401])).

cnf(c_3877,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_402,c_1488])).

cnf(c_93944,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_93943,c_3,c_3877])).

cnf(c_1354,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k4_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_397,c_391])).

cnf(c_6450,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_390,c_1354])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_395,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1220,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_390,c_395])).

cnf(c_6485,plain,
    ( k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6450,c_1220])).

cnf(c_7237,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1110,c_6485])).

cnf(c_7259,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7237,c_3125,c_3644])).

cnf(c_93982,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_93944,c_7259])).

cnf(c_93997,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_93982,c_3125])).

cnf(c_3642,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_397,c_3636])).

cnf(c_11681,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_390,c_3642])).

cnf(c_11715,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_11681,c_1220])).

cnf(c_12063,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11715,c_397])).

cnf(c_20,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_841,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_842,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_12897,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12063,c_20,c_44,c_57,c_842])).

cnf(c_12933,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_12897,c_394])).

cnf(c_2785,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_390,c_2779])).

cnf(c_12946,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_12933,c_2785])).

cnf(c_12947,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12946,c_3,c_3877])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_13097,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12947,c_18])).

cnf(c_13098,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_13097])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_93997,c_13098])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:55:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 43.74/6.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.74/6.01  
% 43.74/6.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.74/6.01  
% 43.74/6.01  ------  iProver source info
% 43.74/6.01  
% 43.74/6.01  git: date: 2020-06-30 10:37:57 +0100
% 43.74/6.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.74/6.01  git: non_committed_changes: false
% 43.74/6.01  git: last_make_outside_of_git: false
% 43.74/6.01  
% 43.74/6.01  ------ 
% 43.74/6.01  ------ Parsing...
% 43.74/6.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.74/6.01  
% 43.74/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 43.74/6.01  
% 43.74/6.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.74/6.01  
% 43.74/6.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.74/6.01  ------ Proving...
% 43.74/6.01  ------ Problem Properties 
% 43.74/6.01  
% 43.74/6.01  
% 43.74/6.01  clauses                                 20
% 43.74/6.01  conjectures                             2
% 43.74/6.01  EPR                                     5
% 43.74/6.01  Horn                                    20
% 43.74/6.01  unary                                   9
% 43.74/6.01  binary                                  7
% 43.74/6.01  lits                                    36
% 43.74/6.01  lits eq                                 14
% 43.74/6.01  fd_pure                                 0
% 43.74/6.01  fd_pseudo                               0
% 43.74/6.01  fd_cond                                 1
% 43.74/6.01  fd_pseudo_cond                          0
% 43.74/6.01  AC symbols                              0
% 43.74/6.01  
% 43.74/6.01  ------ Input Options Time Limit: Unbounded
% 43.74/6.01  
% 43.74/6.01  
% 43.74/6.01  ------ 
% 43.74/6.01  Current options:
% 43.74/6.01  ------ 
% 43.74/6.01  
% 43.74/6.01  
% 43.74/6.01  
% 43.74/6.01  
% 43.74/6.01  ------ Proving...
% 43.74/6.01  
% 43.74/6.01  
% 43.74/6.01  % SZS status Theorem for theBenchmark.p
% 43.74/6.01  
% 43.74/6.01  % SZS output start CNFRefutation for theBenchmark.p
% 43.74/6.01  
% 43.74/6.01  fof(f24,conjecture,(
% 43.74/6.01    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f25,negated_conjecture,(
% 43.74/6.01    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 43.74/6.01    inference(negated_conjecture,[],[f24])).
% 43.74/6.01  
% 43.74/6.01  fof(f39,plain,(
% 43.74/6.01    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f25])).
% 43.74/6.01  
% 43.74/6.01  fof(f40,plain,(
% 43.74/6.01    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 43.74/6.01    introduced(choice_axiom,[])).
% 43.74/6.01  
% 43.74/6.01  fof(f41,plain,(
% 43.74/6.01    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 43.74/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 43.74/6.01  
% 43.74/6.01  fof(f66,plain,(
% 43.74/6.01    v1_relat_1(sK0)),
% 43.74/6.01    inference(cnf_transformation,[],[f41])).
% 43.74/6.01  
% 43.74/6.01  fof(f1,axiom,(
% 43.74/6.01    v1_xboole_0(k1_xboole_0)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f42,plain,(
% 43.74/6.01    v1_xboole_0(k1_xboole_0)),
% 43.74/6.01    inference(cnf_transformation,[],[f1])).
% 43.74/6.01  
% 43.74/6.01  fof(f15,axiom,(
% 43.74/6.01    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f29,plain,(
% 43.74/6.01    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f15])).
% 43.74/6.01  
% 43.74/6.01  fof(f56,plain,(
% 43.74/6.01    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f29])).
% 43.74/6.01  
% 43.74/6.01  fof(f22,axiom,(
% 43.74/6.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f38,plain,(
% 43.74/6.01    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f22])).
% 43.74/6.01  
% 43.74/6.01  fof(f63,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f38])).
% 43.74/6.01  
% 43.74/6.01  fof(f20,axiom,(
% 43.74/6.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f35,plain,(
% 43.74/6.01    ! [X0] : (! [X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f20])).
% 43.74/6.01  
% 43.74/6.01  fof(f61,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f35])).
% 43.74/6.01  
% 43.74/6.01  fof(f2,axiom,(
% 43.74/6.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f26,plain,(
% 43.74/6.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 43.74/6.01    inference(rectify,[],[f2])).
% 43.74/6.01  
% 43.74/6.01  fof(f43,plain,(
% 43.74/6.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 43.74/6.01    inference(cnf_transformation,[],[f26])).
% 43.74/6.01  
% 43.74/6.01  fof(f14,axiom,(
% 43.74/6.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f55,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 43.74/6.01    inference(cnf_transformation,[],[f14])).
% 43.74/6.01  
% 43.74/6.01  fof(f8,axiom,(
% 43.74/6.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f49,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f8])).
% 43.74/6.01  
% 43.74/6.01  fof(f9,axiom,(
% 43.74/6.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f50,plain,(
% 43.74/6.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f9])).
% 43.74/6.01  
% 43.74/6.01  fof(f10,axiom,(
% 43.74/6.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f51,plain,(
% 43.74/6.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f10])).
% 43.74/6.01  
% 43.74/6.01  fof(f11,axiom,(
% 43.74/6.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f52,plain,(
% 43.74/6.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f11])).
% 43.74/6.01  
% 43.74/6.01  fof(f68,plain,(
% 43.74/6.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 43.74/6.01    inference(definition_unfolding,[],[f51,f52])).
% 43.74/6.01  
% 43.74/6.01  fof(f69,plain,(
% 43.74/6.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 43.74/6.01    inference(definition_unfolding,[],[f50,f68])).
% 43.74/6.01  
% 43.74/6.01  fof(f70,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 43.74/6.01    inference(definition_unfolding,[],[f49,f69])).
% 43.74/6.01  
% 43.74/6.01  fof(f71,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 43.74/6.01    inference(definition_unfolding,[],[f55,f70])).
% 43.74/6.01  
% 43.74/6.01  fof(f73,plain,(
% 43.74/6.01    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 43.74/6.01    inference(definition_unfolding,[],[f43,f71])).
% 43.74/6.01  
% 43.74/6.01  fof(f13,axiom,(
% 43.74/6.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f54,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f13])).
% 43.74/6.01  
% 43.74/6.01  fof(f4,axiom,(
% 43.74/6.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f45,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.74/6.01    inference(cnf_transformation,[],[f4])).
% 43.74/6.01  
% 43.74/6.01  fof(f72,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 43.74/6.01    inference(definition_unfolding,[],[f45,f71])).
% 43.74/6.01  
% 43.74/6.01  fof(f75,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1)) )),
% 43.74/6.01    inference(definition_unfolding,[],[f54,f72])).
% 43.74/6.01  
% 43.74/6.01  fof(f7,axiom,(
% 43.74/6.01    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f48,plain,(
% 43.74/6.01    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f7])).
% 43.74/6.01  
% 43.74/6.01  fof(f17,axiom,(
% 43.74/6.01    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f31,plain,(
% 43.74/6.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 43.74/6.01    inference(ennf_transformation,[],[f17])).
% 43.74/6.01  
% 43.74/6.01  fof(f32,plain,(
% 43.74/6.01    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 43.74/6.01    inference(flattening,[],[f31])).
% 43.74/6.01  
% 43.74/6.01  fof(f58,plain,(
% 43.74/6.01    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f32])).
% 43.74/6.01  
% 43.74/6.01  fof(f19,axiom,(
% 43.74/6.01    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f34,plain,(
% 43.74/6.01    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f19])).
% 43.74/6.01  
% 43.74/6.01  fof(f60,plain,(
% 43.74/6.01    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f34])).
% 43.74/6.01  
% 43.74/6.01  fof(f76,plain,(
% 43.74/6.01    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 43.74/6.01    inference(definition_unfolding,[],[f60,f71])).
% 43.74/6.01  
% 43.74/6.01  fof(f16,axiom,(
% 43.74/6.01    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f30,plain,(
% 43.74/6.01    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f16])).
% 43.74/6.01  
% 43.74/6.01  fof(f57,plain,(
% 43.74/6.01    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f30])).
% 43.74/6.01  
% 43.74/6.01  fof(f23,axiom,(
% 43.74/6.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f65,plain,(
% 43.74/6.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 43.74/6.01    inference(cnf_transformation,[],[f23])).
% 43.74/6.01  
% 43.74/6.01  fof(f21,axiom,(
% 43.74/6.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f36,plain,(
% 43.74/6.01    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f21])).
% 43.74/6.01  
% 43.74/6.01  fof(f37,plain,(
% 43.74/6.01    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 43.74/6.01    inference(flattening,[],[f36])).
% 43.74/6.01  
% 43.74/6.01  fof(f62,plain,(
% 43.74/6.01    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f37])).
% 43.74/6.01  
% 43.74/6.01  fof(f64,plain,(
% 43.74/6.01    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 43.74/6.01    inference(cnf_transformation,[],[f23])).
% 43.74/6.01  
% 43.74/6.01  fof(f6,axiom,(
% 43.74/6.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f47,plain,(
% 43.74/6.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f6])).
% 43.74/6.01  
% 43.74/6.01  fof(f5,axiom,(
% 43.74/6.01    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f46,plain,(
% 43.74/6.01    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f5])).
% 43.74/6.01  
% 43.74/6.01  fof(f74,plain,(
% 43.74/6.01    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 43.74/6.01    inference(definition_unfolding,[],[f46,f71])).
% 43.74/6.01  
% 43.74/6.01  fof(f12,axiom,(
% 43.74/6.01    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f28,plain,(
% 43.74/6.01    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f12])).
% 43.74/6.01  
% 43.74/6.01  fof(f53,plain,(
% 43.74/6.01    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f28])).
% 43.74/6.01  
% 43.74/6.01  fof(f3,axiom,(
% 43.74/6.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f27,plain,(
% 43.74/6.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f3])).
% 43.74/6.01  
% 43.74/6.01  fof(f44,plain,(
% 43.74/6.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f27])).
% 43.74/6.01  
% 43.74/6.01  fof(f18,axiom,(
% 43.74/6.01    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 43.74/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.74/6.01  
% 43.74/6.01  fof(f33,plain,(
% 43.74/6.01    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 43.74/6.01    inference(ennf_transformation,[],[f18])).
% 43.74/6.01  
% 43.74/6.01  fof(f59,plain,(
% 43.74/6.01    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 43.74/6.01    inference(cnf_transformation,[],[f33])).
% 43.74/6.01  
% 43.74/6.01  fof(f67,plain,(
% 43.74/6.01    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 43.74/6.01    inference(cnf_transformation,[],[f41])).
% 43.74/6.01  
% 43.74/6.01  cnf(c_19,negated_conjecture,
% 43.74/6.01      ( v1_relat_1(sK0) ),
% 43.74/6.01      inference(cnf_transformation,[],[f66]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_390,plain,
% 43.74/6.01      ( v1_relat_1(sK0) = iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_0,plain,
% 43.74/6.01      ( v1_xboole_0(k1_xboole_0) ),
% 43.74/6.01      inference(cnf_transformation,[],[f42]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_402,plain,
% 43.74/6.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_8,plain,
% 43.74/6.01      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 43.74/6.01      inference(cnf_transformation,[],[f56]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_398,plain,
% 43.74/6.01      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_1110,plain,
% 43.74/6.01      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_402,c_398]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_15,plain,
% 43.74/6.01      ( ~ v1_relat_1(X0)
% 43.74/6.01      | ~ v1_relat_1(X1)
% 43.74/6.01      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 43.74/6.01      inference(cnf_transformation,[],[f63]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_391,plain,
% 43.74/6.01      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 43.74/6.01      | v1_relat_1(X1) != iProver_top
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_1115,plain,
% 43.74/6.01      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_1110,c_391]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_13,plain,
% 43.74/6.01      ( ~ v1_relat_1(X0)
% 43.74/6.01      | ~ v1_relat_1(X1)
% 43.74/6.01      | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
% 43.74/6.01      inference(cnf_transformation,[],[f61]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_393,plain,
% 43.74/6.01      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
% 43.74/6.01      | v1_relat_1(X0) != iProver_top
% 43.74/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_2393,plain,
% 43.74/6.01      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_390,c_393]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_3114,plain,
% 43.74/6.01      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_390,c_2393]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_1,plain,
% 43.74/6.01      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
% 43.74/6.01      inference(cnf_transformation,[],[f73]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_7,plain,
% 43.74/6.01      ( k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
% 43.74/6.01      inference(cnf_transformation,[],[f75]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_799,plain,
% 43.74/6.01      ( k6_subset_1(X0,X0) = k5_xboole_0(X0,X0) ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_5,plain,
% 43.74/6.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 43.74/6.01      inference(cnf_transformation,[],[f48]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_804,plain,
% 43.74/6.01      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_799,c_5]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_3125,plain,
% 43.74/6.01      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 43.74/6.01      inference(demodulation,[status(thm)],[c_3114,c_804]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_3636,plain,
% 43.74/6.01      ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_1115,c_3125]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_3644,plain,
% 43.74/6.01      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_390,c_3636]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_10,plain,
% 43.74/6.01      ( ~ v1_relat_1(X0)
% 43.74/6.01      | ~ v1_relat_1(X1)
% 43.74/6.01      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 43.74/6.01      inference(cnf_transformation,[],[f58]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_396,plain,
% 43.74/6.01      ( v1_relat_1(X0) != iProver_top
% 43.74/6.01      | v1_relat_1(X1) != iProver_top
% 43.74/6.01      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_3872,plain,
% 43.74/6.01      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 43.74/6.01      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 43.74/6.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_3644,c_396]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_42,plain,
% 43.74/6.01      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_44,plain,
% 43.74/6.01      ( v1_relat_1(k1_xboole_0) = iProver_top
% 43.74/6.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 43.74/6.01      inference(instantiation,[status(thm)],[c_42]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_57,plain,
% 43.74/6.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_4142,plain,
% 43.74/6.01      ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 43.74/6.01      | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 43.74/6.01      inference(global_propositional_subsumption,
% 43.74/6.01                [status(thm)],
% 43.74/6.01                [c_3872,c_44,c_57]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_4143,plain,
% 43.74/6.01      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 43.74/6.01      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 43.74/6.01      inference(renaming,[status(thm)],[c_4142]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_12,plain,
% 43.74/6.01      ( ~ v1_relat_1(X0)
% 43.74/6.01      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 43.74/6.01      inference(cnf_transformation,[],[f76]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_394,plain,
% 43.74/6.01      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_4157,plain,
% 43.74/6.01      ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 43.74/6.01      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_4143,c_394]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_4232,plain,
% 43.74/6.01      ( ~ v1_relat_1(k4_relat_1(sK0))
% 43.74/6.01      | k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 43.74/6.01      inference(predicate_to_equality_rev,[status(thm)],[c_4157]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_9,plain,
% 43.74/6.01      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 43.74/6.01      inference(cnf_transformation,[],[f57]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_9838,plain,
% 43.74/6.01      ( v1_relat_1(k4_relat_1(sK0)) | ~ v1_relat_1(sK0) ),
% 43.74/6.01      inference(instantiation,[status(thm)],[c_9]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_93941,plain,
% 43.74/6.01      ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 43.74/6.01      inference(global_propositional_subsumption,
% 43.74/6.01                [status(thm)],
% 43.74/6.01                [c_4157,c_19,c_4232,c_9838]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_397,plain,
% 43.74/6.01      ( v1_relat_1(X0) != iProver_top
% 43.74/6.01      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_16,plain,
% 43.74/6.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 43.74/6.01      inference(cnf_transformation,[],[f65]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_14,plain,
% 43.74/6.01      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 43.74/6.01      | ~ v1_relat_1(X0)
% 43.74/6.01      | ~ v1_relat_1(X1)
% 43.74/6.01      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 43.74/6.01      inference(cnf_transformation,[],[f62]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_392,plain,
% 43.74/6.01      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 43.74/6.01      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 43.74/6.01      | v1_relat_1(X0) != iProver_top
% 43.74/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_1324,plain,
% 43.74/6.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 43.74/6.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 43.74/6.01      | v1_relat_1(X0) != iProver_top
% 43.74/6.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_16,c_392]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_17,plain,
% 43.74/6.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 43.74/6.01      inference(cnf_transformation,[],[f64]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_1338,plain,
% 43.74/6.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 43.74/6.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 43.74/6.01      | v1_relat_1(X0) != iProver_top
% 43.74/6.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_1324,c_17]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_2772,plain,
% 43.74/6.01      ( v1_relat_1(X0) != iProver_top
% 43.74/6.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 43.74/6.01      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 43.74/6.01      inference(global_propositional_subsumption,
% 43.74/6.01                [status(thm)],
% 43.74/6.01                [c_1338,c_44,c_57]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_2773,plain,
% 43.74/6.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 43.74/6.01      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(renaming,[status(thm)],[c_2772]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_4,plain,
% 43.74/6.01      ( r1_tarski(k1_xboole_0,X0) ),
% 43.74/6.01      inference(cnf_transformation,[],[f47]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_400,plain,
% 43.74/6.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_2779,plain,
% 43.74/6.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(forward_subsumption_resolution,
% 43.74/6.01                [status(thm)],
% 43.74/6.01                [c_2773,c_400]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_2783,plain,
% 43.74/6.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_397,c_2779]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_5369,plain,
% 43.74/6.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_390,c_2783]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_5394,plain,
% 43.74/6.01      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_5369,c_3644]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_93943,plain,
% 43.74/6.01      ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_93941,c_5394]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_3,plain,
% 43.74/6.01      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 43.74/6.01      inference(cnf_transformation,[],[f74]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_6,plain,
% 43.74/6.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 43.74/6.01      inference(cnf_transformation,[],[f53]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_399,plain,
% 43.74/6.01      ( v1_xboole_0(X0) != iProver_top
% 43.74/6.01      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_2,plain,
% 43.74/6.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 43.74/6.01      inference(cnf_transformation,[],[f44]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_401,plain,
% 43.74/6.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_1488,plain,
% 43.74/6.01      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 43.74/6.01      | v1_xboole_0(X0) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_399,c_401]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_3877,plain,
% 43.74/6.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_402,c_1488]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_93944,plain,
% 43.74/6.01      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 43.74/6.01      inference(demodulation,[status(thm)],[c_93943,c_3,c_3877]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_1354,plain,
% 43.74/6.01      ( k5_relat_1(k4_relat_1(k4_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k4_relat_1(X0)))
% 43.74/6.01      | v1_relat_1(X0) != iProver_top
% 43.74/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_397,c_391]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_6450,plain,
% 43.74/6.01      ( k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_390,c_1354]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_11,plain,
% 43.74/6.01      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 43.74/6.01      inference(cnf_transformation,[],[f59]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_395,plain,
% 43.74/6.01      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_1220,plain,
% 43.74/6.01      ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_390,c_395]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_6485,plain,
% 43.74/6.01      ( k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X0))
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_6450,c_1220]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_7237,plain,
% 43.74/6.01      ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_1110,c_6485]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_7259,plain,
% 43.74/6.01      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_7237,c_3125,c_3644]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_93982,plain,
% 43.74/6.01      ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) ),
% 43.74/6.01      inference(demodulation,[status(thm)],[c_93944,c_7259]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_93997,plain,
% 43.74/6.01      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_93982,c_3125]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_3642,plain,
% 43.74/6.01      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
% 43.74/6.01      | v1_relat_1(X0) != iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_397,c_3636]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_11681,plain,
% 43.74/6.01      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_390,c_3642]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_11715,plain,
% 43.74/6.01      ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,sK0) ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_11681,c_1220]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_12063,plain,
% 43.74/6.01      ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
% 43.74/6.01      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_11715,c_397]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_20,plain,
% 43.74/6.01      ( v1_relat_1(sK0) = iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_841,plain,
% 43.74/6.01      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 43.74/6.01      | ~ v1_relat_1(sK0)
% 43.74/6.01      | ~ v1_relat_1(k1_xboole_0) ),
% 43.74/6.01      inference(instantiation,[status(thm)],[c_10]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_842,plain,
% 43.74/6.01      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 43.74/6.01      | v1_relat_1(sK0) != iProver_top
% 43.74/6.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 43.74/6.01      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_12897,plain,
% 43.74/6.01      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 43.74/6.01      inference(global_propositional_subsumption,
% 43.74/6.01                [status(thm)],
% 43.74/6.01                [c_12063,c_20,c_44,c_57,c_842]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_12933,plain,
% 43.74/6.01      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_12897,c_394]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_2785,plain,
% 43.74/6.01      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 43.74/6.01      inference(superposition,[status(thm)],[c_390,c_2779]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_12946,plain,
% 43.74/6.01      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 43.74/6.01      inference(light_normalisation,[status(thm)],[c_12933,c_2785]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_12947,plain,
% 43.74/6.01      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 43.74/6.01      inference(demodulation,[status(thm)],[c_12946,c_3,c_3877]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_18,negated_conjecture,
% 43.74/6.01      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 43.74/6.01      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 43.74/6.01      inference(cnf_transformation,[],[f67]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_13097,plain,
% 43.74/6.01      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 43.74/6.01      | k1_xboole_0 != k1_xboole_0 ),
% 43.74/6.01      inference(demodulation,[status(thm)],[c_12947,c_18]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(c_13098,plain,
% 43.74/6.01      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 43.74/6.01      inference(equality_resolution_simp,[status(thm)],[c_13097]) ).
% 43.74/6.01  
% 43.74/6.01  cnf(contradiction,plain,
% 43.74/6.01      ( $false ),
% 43.74/6.01      inference(minisat,[status(thm)],[c_93997,c_13098]) ).
% 43.74/6.01  
% 43.74/6.01  
% 43.74/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.74/6.01  
% 43.74/6.01  ------                               Statistics
% 43.74/6.01  
% 43.74/6.01  ------ Selected
% 43.74/6.01  
% 43.74/6.01  total_time:                             5.296
% 43.74/6.01  
%------------------------------------------------------------------------------
