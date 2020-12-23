%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:58 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 644 expanded)
%              Number of clauses        :   87 ( 238 expanded)
%              Number of leaves         :   20 ( 146 expanded)
%              Depth                    :   24
%              Number of atoms          :  315 (1311 expanded)
%              Number of equality atoms :  215 ( 817 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f32,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f37])).

fof(f64,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f46,f52,f52])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X0] :
      ( k6_subset_1(X0,k6_subset_1(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_22,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_453,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_460,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_465,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_461,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1178,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_465,c_461])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_454,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1635,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_454])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_456,plain,
    ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1082,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_456])).

cnf(c_2086,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_453,c_1082])).

cnf(c_4,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_484,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_6])).

cnf(c_2092,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2086,c_484])).

cnf(c_2863,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1635,c_2092])).

cnf(c_2869,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_2863])).

cnf(c_3282,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_453,c_2869])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_458,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1183,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_453,c_458])).

cnf(c_3292,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_3282,c_1183])).

cnf(c_24758,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3292,c_460])).

cnf(c_23,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_45,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_47,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_61,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1140,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1141,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1140])).

cnf(c_24761,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24758,c_23,c_47,c_61,c_1141])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(X0,k6_subset_1(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_457,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_24896,plain,
    ( k6_subset_1(k5_relat_1(k1_xboole_0,sK0),k6_subset_1(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_24761,c_457])).

cnf(c_20,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_455,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_859,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_455])).

cnf(c_1620,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_859,c_47,c_61])).

cnf(c_1621,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1620])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_462,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_464,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1443,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_462,c_464])).

cnf(c_1930,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1621,c_1443])).

cnf(c_8270,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_453,c_1930])).

cnf(c_24911,plain,
    ( k6_subset_1(k5_relat_1(k1_xboole_0,sK0),k6_subset_1(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_24896,c_8270])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24912,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24911,c_6,c_8,c_484])).

cnf(c_217,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_12716,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_12717,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12716])).

cnf(c_459,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1466,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_459,c_458])).

cnf(c_4975,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_1466])).

cnf(c_5258,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1178,c_4975])).

cnf(c_2871,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_453,c_2863])).

cnf(c_2901,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2871,c_459])).

cnf(c_4689,plain,
    ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2901,c_47,c_61])).

cnf(c_4690,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4689])).

cnf(c_4710,plain,
    ( k6_subset_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k6_subset_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4690,c_457])).

cnf(c_1444,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_455,c_464])).

cnf(c_4023,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2871,c_1444])).

cnf(c_4028,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4023,c_20,c_2871])).

cnf(c_4044,plain,
    ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4028,c_47,c_61])).

cnf(c_4045,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4044])).

cnf(c_4051,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4045,c_462])).

cnf(c_4053,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_4051])).

cnf(c_4299,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4053,c_23])).

cnf(c_4732,plain,
    ( k6_subset_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k6_subset_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4710,c_4299])).

cnf(c_4733,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4732,c_6,c_8,c_484])).

cnf(c_4967,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_4733])).

cnf(c_5243,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4967,c_23])).

cnf(c_5265,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5258,c_2092,c_5243])).

cnf(c_615,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_616,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_50,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_49,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24912,c_12717,c_5265,c_616,c_50,c_49,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.67/1.55  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.67/1.55  
% 7.67/1.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.55  
% 7.67/1.55  ------  iProver source info
% 7.67/1.55  
% 7.67/1.55  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.55  git: non_committed_changes: false
% 7.67/1.55  git: last_make_outside_of_git: false
% 7.67/1.55  
% 7.67/1.55  ------ 
% 7.67/1.55  
% 7.67/1.55  ------ Input Options
% 7.67/1.55  
% 7.67/1.55  --out_options                           all
% 7.67/1.55  --tptp_safe_out                         true
% 7.67/1.55  --problem_path                          ""
% 7.67/1.55  --include_path                          ""
% 7.67/1.55  --clausifier                            res/vclausify_rel
% 7.67/1.55  --clausifier_options                    --mode clausify
% 7.67/1.55  --stdin                                 false
% 7.67/1.55  --stats_out                             sel
% 7.67/1.55  
% 7.67/1.55  ------ General Options
% 7.67/1.55  
% 7.67/1.55  --fof                                   false
% 7.67/1.55  --time_out_real                         604.97
% 7.67/1.55  --time_out_virtual                      -1.
% 7.67/1.55  --symbol_type_check                     false
% 7.67/1.55  --clausify_out                          false
% 7.67/1.55  --sig_cnt_out                           false
% 7.67/1.55  --trig_cnt_out                          false
% 7.67/1.55  --trig_cnt_out_tolerance                1.
% 7.67/1.55  --trig_cnt_out_sk_spl                   false
% 7.67/1.55  --abstr_cl_out                          false
% 7.67/1.55  
% 7.67/1.55  ------ Global Options
% 7.67/1.55  
% 7.67/1.55  --schedule                              none
% 7.67/1.55  --add_important_lit                     false
% 7.67/1.55  --prop_solver_per_cl                    1000
% 7.67/1.55  --min_unsat_core                        false
% 7.67/1.55  --soft_assumptions                      false
% 7.67/1.55  --soft_lemma_size                       3
% 7.67/1.55  --prop_impl_unit_size                   0
% 7.67/1.55  --prop_impl_unit                        []
% 7.67/1.55  --share_sel_clauses                     true
% 7.67/1.55  --reset_solvers                         false
% 7.67/1.55  --bc_imp_inh                            [conj_cone]
% 7.67/1.55  --conj_cone_tolerance                   3.
% 7.67/1.55  --extra_neg_conj                        none
% 7.67/1.55  --large_theory_mode                     true
% 7.67/1.55  --prolific_symb_bound                   200
% 7.67/1.55  --lt_threshold                          2000
% 7.67/1.55  --clause_weak_htbl                      true
% 7.67/1.55  --gc_record_bc_elim                     false
% 7.67/1.55  
% 7.67/1.55  ------ Preprocessing Options
% 7.67/1.55  
% 7.67/1.55  --preprocessing_flag                    true
% 7.67/1.55  --time_out_prep_mult                    0.1
% 7.67/1.55  --splitting_mode                        input
% 7.67/1.55  --splitting_grd                         true
% 7.67/1.55  --splitting_cvd                         false
% 7.67/1.55  --splitting_cvd_svl                     false
% 7.67/1.55  --splitting_nvd                         32
% 7.67/1.55  --sub_typing                            true
% 7.67/1.55  --prep_gs_sim                           false
% 7.67/1.55  --prep_unflatten                        true
% 7.67/1.55  --prep_res_sim                          true
% 7.67/1.55  --prep_upred                            true
% 7.67/1.55  --prep_sem_filter                       exhaustive
% 7.67/1.55  --prep_sem_filter_out                   false
% 7.67/1.55  --pred_elim                             false
% 7.67/1.55  --res_sim_input                         true
% 7.67/1.55  --eq_ax_congr_red                       true
% 7.67/1.55  --pure_diseq_elim                       true
% 7.67/1.55  --brand_transform                       false
% 7.67/1.55  --non_eq_to_eq                          false
% 7.67/1.55  --prep_def_merge                        true
% 7.67/1.55  --prep_def_merge_prop_impl              false
% 7.67/1.55  --prep_def_merge_mbd                    true
% 7.67/1.55  --prep_def_merge_tr_red                 false
% 7.67/1.55  --prep_def_merge_tr_cl                  false
% 7.67/1.55  --smt_preprocessing                     true
% 7.67/1.55  --smt_ac_axioms                         fast
% 7.67/1.55  --preprocessed_out                      false
% 7.67/1.55  --preprocessed_stats                    false
% 7.67/1.55  
% 7.67/1.55  ------ Abstraction refinement Options
% 7.67/1.55  
% 7.67/1.55  --abstr_ref                             []
% 7.67/1.55  --abstr_ref_prep                        false
% 7.67/1.55  --abstr_ref_until_sat                   false
% 7.67/1.55  --abstr_ref_sig_restrict                funpre
% 7.67/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.55  --abstr_ref_under                       []
% 7.67/1.55  
% 7.67/1.55  ------ SAT Options
% 7.67/1.55  
% 7.67/1.55  --sat_mode                              false
% 7.67/1.55  --sat_fm_restart_options                ""
% 7.67/1.55  --sat_gr_def                            false
% 7.67/1.55  --sat_epr_types                         true
% 7.67/1.55  --sat_non_cyclic_types                  false
% 7.67/1.55  --sat_finite_models                     false
% 7.67/1.55  --sat_fm_lemmas                         false
% 7.67/1.55  --sat_fm_prep                           false
% 7.67/1.55  --sat_fm_uc_incr                        true
% 7.67/1.55  --sat_out_model                         small
% 7.67/1.55  --sat_out_clauses                       false
% 7.67/1.55  
% 7.67/1.55  ------ QBF Options
% 7.67/1.55  
% 7.67/1.55  --qbf_mode                              false
% 7.67/1.55  --qbf_elim_univ                         false
% 7.67/1.55  --qbf_dom_inst                          none
% 7.67/1.55  --qbf_dom_pre_inst                      false
% 7.67/1.55  --qbf_sk_in                             false
% 7.67/1.55  --qbf_pred_elim                         true
% 7.67/1.55  --qbf_split                             512
% 7.67/1.55  
% 7.67/1.55  ------ BMC1 Options
% 7.67/1.55  
% 7.67/1.55  --bmc1_incremental                      false
% 7.67/1.55  --bmc1_axioms                           reachable_all
% 7.67/1.55  --bmc1_min_bound                        0
% 7.67/1.55  --bmc1_max_bound                        -1
% 7.67/1.55  --bmc1_max_bound_default                -1
% 7.67/1.55  --bmc1_symbol_reachability              true
% 7.67/1.55  --bmc1_property_lemmas                  false
% 7.67/1.55  --bmc1_k_induction                      false
% 7.67/1.55  --bmc1_non_equiv_states                 false
% 7.67/1.55  --bmc1_deadlock                         false
% 7.67/1.55  --bmc1_ucm                              false
% 7.67/1.55  --bmc1_add_unsat_core                   none
% 7.67/1.55  --bmc1_unsat_core_children              false
% 7.67/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.55  --bmc1_out_stat                         full
% 7.67/1.55  --bmc1_ground_init                      false
% 7.67/1.55  --bmc1_pre_inst_next_state              false
% 7.67/1.55  --bmc1_pre_inst_state                   false
% 7.67/1.55  --bmc1_pre_inst_reach_state             false
% 7.67/1.55  --bmc1_out_unsat_core                   false
% 7.67/1.55  --bmc1_aig_witness_out                  false
% 7.67/1.55  --bmc1_verbose                          false
% 7.67/1.55  --bmc1_dump_clauses_tptp                false
% 7.67/1.55  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.55  --bmc1_dump_file                        -
% 7.67/1.55  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.55  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.55  --bmc1_ucm_extend_mode                  1
% 7.67/1.55  --bmc1_ucm_init_mode                    2
% 7.67/1.55  --bmc1_ucm_cone_mode                    none
% 7.67/1.55  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.55  --bmc1_ucm_relax_model                  4
% 7.67/1.55  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.55  --bmc1_ucm_layered_model                none
% 7.67/1.55  --bmc1_ucm_max_lemma_size               10
% 7.67/1.55  
% 7.67/1.55  ------ AIG Options
% 7.67/1.55  
% 7.67/1.55  --aig_mode                              false
% 7.67/1.55  
% 7.67/1.55  ------ Instantiation Options
% 7.67/1.55  
% 7.67/1.55  --instantiation_flag                    true
% 7.67/1.55  --inst_sos_flag                         false
% 7.67/1.55  --inst_sos_phase                        true
% 7.67/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.55  --inst_lit_sel_side                     num_symb
% 7.67/1.55  --inst_solver_per_active                1400
% 7.67/1.55  --inst_solver_calls_frac                1.
% 7.67/1.55  --inst_passive_queue_type               priority_queues
% 7.67/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.55  --inst_passive_queues_freq              [25;2]
% 7.67/1.55  --inst_dismatching                      true
% 7.67/1.55  --inst_eager_unprocessed_to_passive     true
% 7.67/1.55  --inst_prop_sim_given                   true
% 7.67/1.55  --inst_prop_sim_new                     false
% 7.67/1.55  --inst_subs_new                         false
% 7.67/1.55  --inst_eq_res_simp                      false
% 7.67/1.55  --inst_subs_given                       false
% 7.67/1.55  --inst_orphan_elimination               true
% 7.67/1.55  --inst_learning_loop_flag               true
% 7.67/1.55  --inst_learning_start                   3000
% 7.67/1.55  --inst_learning_factor                  2
% 7.67/1.55  --inst_start_prop_sim_after_learn       3
% 7.67/1.55  --inst_sel_renew                        solver
% 7.67/1.55  --inst_lit_activity_flag                true
% 7.67/1.55  --inst_restr_to_given                   false
% 7.67/1.55  --inst_activity_threshold               500
% 7.67/1.55  --inst_out_proof                        true
% 7.67/1.55  
% 7.67/1.55  ------ Resolution Options
% 7.67/1.55  
% 7.67/1.55  --resolution_flag                       true
% 7.67/1.55  --res_lit_sel                           adaptive
% 7.67/1.55  --res_lit_sel_side                      none
% 7.67/1.55  --res_ordering                          kbo
% 7.67/1.55  --res_to_prop_solver                    active
% 7.67/1.55  --res_prop_simpl_new                    false
% 7.67/1.55  --res_prop_simpl_given                  true
% 7.67/1.55  --res_passive_queue_type                priority_queues
% 7.67/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.55  --res_passive_queues_freq               [15;5]
% 7.67/1.55  --res_forward_subs                      full
% 7.67/1.55  --res_backward_subs                     full
% 7.67/1.55  --res_forward_subs_resolution           true
% 7.67/1.55  --res_backward_subs_resolution          true
% 7.67/1.55  --res_orphan_elimination                true
% 7.67/1.55  --res_time_limit                        2.
% 7.67/1.55  --res_out_proof                         true
% 7.67/1.55  
% 7.67/1.55  ------ Superposition Options
% 7.67/1.55  
% 7.67/1.55  --superposition_flag                    true
% 7.67/1.55  --sup_passive_queue_type                priority_queues
% 7.67/1.55  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.55  --sup_passive_queues_freq               [1;4]
% 7.67/1.55  --demod_completeness_check              fast
% 7.67/1.55  --demod_use_ground                      true
% 7.67/1.55  --sup_to_prop_solver                    passive
% 7.67/1.55  --sup_prop_simpl_new                    true
% 7.67/1.55  --sup_prop_simpl_given                  true
% 7.67/1.55  --sup_fun_splitting                     false
% 7.67/1.55  --sup_smt_interval                      50000
% 7.67/1.55  
% 7.67/1.55  ------ Superposition Simplification Setup
% 7.67/1.55  
% 7.67/1.55  --sup_indices_passive                   []
% 7.67/1.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.55  --sup_full_bw                           [BwDemod]
% 7.67/1.55  --sup_immed_triv                        [TrivRules]
% 7.67/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.55  --sup_immed_bw_main                     []
% 7.67/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.55  
% 7.67/1.55  ------ Combination Options
% 7.67/1.55  
% 7.67/1.55  --comb_res_mult                         3
% 7.67/1.55  --comb_sup_mult                         2
% 7.67/1.55  --comb_inst_mult                        10
% 7.67/1.55  
% 7.67/1.55  ------ Debug Options
% 7.67/1.55  
% 7.67/1.55  --dbg_backtrace                         false
% 7.67/1.55  --dbg_dump_prop_clauses                 false
% 7.67/1.55  --dbg_dump_prop_clauses_file            -
% 7.67/1.55  --dbg_out_stat                          false
% 7.67/1.55  ------ Parsing...
% 7.67/1.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.55  
% 7.67/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.67/1.55  
% 7.67/1.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.55  
% 7.67/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.55  ------ Proving...
% 7.67/1.55  ------ Problem Properties 
% 7.67/1.55  
% 7.67/1.55  
% 7.67/1.55  clauses                                 22
% 7.67/1.55  conjectures                             2
% 7.67/1.55  EPR                                     6
% 7.67/1.55  Horn                                    21
% 7.67/1.55  unary                                   11
% 7.67/1.55  binary                                  5
% 7.67/1.55  lits                                    39
% 7.67/1.55  lits eq                                 17
% 7.67/1.55  fd_pure                                 0
% 7.67/1.55  fd_pseudo                               0
% 7.67/1.55  fd_cond                                 1
% 7.67/1.55  fd_pseudo_cond                          1
% 7.67/1.55  AC symbols                              0
% 7.67/1.55  
% 7.67/1.55  ------ Input Options Time Limit: Unbounded
% 7.67/1.55  
% 7.67/1.55  
% 7.67/1.55  ------ 
% 7.67/1.55  Current options:
% 7.67/1.55  ------ 
% 7.67/1.55  
% 7.67/1.55  ------ Input Options
% 7.67/1.55  
% 7.67/1.55  --out_options                           all
% 7.67/1.55  --tptp_safe_out                         true
% 7.67/1.55  --problem_path                          ""
% 7.67/1.55  --include_path                          ""
% 7.67/1.55  --clausifier                            res/vclausify_rel
% 7.67/1.55  --clausifier_options                    --mode clausify
% 7.67/1.55  --stdin                                 false
% 7.67/1.55  --stats_out                             sel
% 7.67/1.55  
% 7.67/1.55  ------ General Options
% 7.67/1.55  
% 7.67/1.55  --fof                                   false
% 7.67/1.55  --time_out_real                         604.97
% 7.67/1.55  --time_out_virtual                      -1.
% 7.67/1.55  --symbol_type_check                     false
% 7.67/1.55  --clausify_out                          false
% 7.67/1.55  --sig_cnt_out                           false
% 7.67/1.55  --trig_cnt_out                          false
% 7.67/1.55  --trig_cnt_out_tolerance                1.
% 7.67/1.55  --trig_cnt_out_sk_spl                   false
% 7.67/1.55  --abstr_cl_out                          false
% 7.67/1.55  
% 7.67/1.55  ------ Global Options
% 7.67/1.55  
% 7.67/1.55  --schedule                              none
% 7.67/1.55  --add_important_lit                     false
% 7.67/1.55  --prop_solver_per_cl                    1000
% 7.67/1.55  --min_unsat_core                        false
% 7.67/1.55  --soft_assumptions                      false
% 7.67/1.55  --soft_lemma_size                       3
% 7.67/1.55  --prop_impl_unit_size                   0
% 7.67/1.55  --prop_impl_unit                        []
% 7.67/1.55  --share_sel_clauses                     true
% 7.67/1.55  --reset_solvers                         false
% 7.67/1.55  --bc_imp_inh                            [conj_cone]
% 7.67/1.55  --conj_cone_tolerance                   3.
% 7.67/1.55  --extra_neg_conj                        none
% 7.67/1.55  --large_theory_mode                     true
% 7.67/1.55  --prolific_symb_bound                   200
% 7.67/1.55  --lt_threshold                          2000
% 7.67/1.55  --clause_weak_htbl                      true
% 7.67/1.55  --gc_record_bc_elim                     false
% 7.67/1.55  
% 7.67/1.55  ------ Preprocessing Options
% 7.67/1.55  
% 7.67/1.55  --preprocessing_flag                    true
% 7.67/1.55  --time_out_prep_mult                    0.1
% 7.67/1.55  --splitting_mode                        input
% 7.67/1.55  --splitting_grd                         true
% 7.67/1.55  --splitting_cvd                         false
% 7.67/1.55  --splitting_cvd_svl                     false
% 7.67/1.55  --splitting_nvd                         32
% 7.67/1.55  --sub_typing                            true
% 7.67/1.55  --prep_gs_sim                           false
% 7.67/1.55  --prep_unflatten                        true
% 7.67/1.55  --prep_res_sim                          true
% 7.67/1.55  --prep_upred                            true
% 7.67/1.55  --prep_sem_filter                       exhaustive
% 7.67/1.55  --prep_sem_filter_out                   false
% 7.67/1.55  --pred_elim                             false
% 7.67/1.55  --res_sim_input                         true
% 7.67/1.55  --eq_ax_congr_red                       true
% 7.67/1.55  --pure_diseq_elim                       true
% 7.67/1.55  --brand_transform                       false
% 7.67/1.55  --non_eq_to_eq                          false
% 7.67/1.55  --prep_def_merge                        true
% 7.67/1.55  --prep_def_merge_prop_impl              false
% 7.67/1.55  --prep_def_merge_mbd                    true
% 7.67/1.55  --prep_def_merge_tr_red                 false
% 7.67/1.55  --prep_def_merge_tr_cl                  false
% 7.67/1.55  --smt_preprocessing                     true
% 7.67/1.55  --smt_ac_axioms                         fast
% 7.67/1.55  --preprocessed_out                      false
% 7.67/1.55  --preprocessed_stats                    false
% 7.67/1.55  
% 7.67/1.55  ------ Abstraction refinement Options
% 7.67/1.55  
% 7.67/1.55  --abstr_ref                             []
% 7.67/1.55  --abstr_ref_prep                        false
% 7.67/1.55  --abstr_ref_until_sat                   false
% 7.67/1.55  --abstr_ref_sig_restrict                funpre
% 7.67/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.55  --abstr_ref_under                       []
% 7.67/1.55  
% 7.67/1.55  ------ SAT Options
% 7.67/1.55  
% 7.67/1.55  --sat_mode                              false
% 7.67/1.55  --sat_fm_restart_options                ""
% 7.67/1.55  --sat_gr_def                            false
% 7.67/1.55  --sat_epr_types                         true
% 7.67/1.55  --sat_non_cyclic_types                  false
% 7.67/1.55  --sat_finite_models                     false
% 7.67/1.55  --sat_fm_lemmas                         false
% 7.67/1.55  --sat_fm_prep                           false
% 7.67/1.55  --sat_fm_uc_incr                        true
% 7.67/1.55  --sat_out_model                         small
% 7.67/1.55  --sat_out_clauses                       false
% 7.67/1.55  
% 7.67/1.55  ------ QBF Options
% 7.67/1.55  
% 7.67/1.55  --qbf_mode                              false
% 7.67/1.55  --qbf_elim_univ                         false
% 7.67/1.55  --qbf_dom_inst                          none
% 7.67/1.55  --qbf_dom_pre_inst                      false
% 7.67/1.55  --qbf_sk_in                             false
% 7.67/1.55  --qbf_pred_elim                         true
% 7.67/1.55  --qbf_split                             512
% 7.67/1.55  
% 7.67/1.55  ------ BMC1 Options
% 7.67/1.55  
% 7.67/1.55  --bmc1_incremental                      false
% 7.67/1.55  --bmc1_axioms                           reachable_all
% 7.67/1.55  --bmc1_min_bound                        0
% 7.67/1.55  --bmc1_max_bound                        -1
% 7.67/1.55  --bmc1_max_bound_default                -1
% 7.67/1.55  --bmc1_symbol_reachability              true
% 7.67/1.55  --bmc1_property_lemmas                  false
% 7.67/1.55  --bmc1_k_induction                      false
% 7.67/1.55  --bmc1_non_equiv_states                 false
% 7.67/1.55  --bmc1_deadlock                         false
% 7.67/1.55  --bmc1_ucm                              false
% 7.67/1.55  --bmc1_add_unsat_core                   none
% 7.67/1.55  --bmc1_unsat_core_children              false
% 7.67/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.55  --bmc1_out_stat                         full
% 7.67/1.55  --bmc1_ground_init                      false
% 7.67/1.55  --bmc1_pre_inst_next_state              false
% 7.67/1.55  --bmc1_pre_inst_state                   false
% 7.67/1.55  --bmc1_pre_inst_reach_state             false
% 7.67/1.55  --bmc1_out_unsat_core                   false
% 7.67/1.55  --bmc1_aig_witness_out                  false
% 7.67/1.55  --bmc1_verbose                          false
% 7.67/1.55  --bmc1_dump_clauses_tptp                false
% 7.67/1.55  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.55  --bmc1_dump_file                        -
% 7.67/1.55  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.55  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.55  --bmc1_ucm_extend_mode                  1
% 7.67/1.55  --bmc1_ucm_init_mode                    2
% 7.67/1.55  --bmc1_ucm_cone_mode                    none
% 7.67/1.55  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.55  --bmc1_ucm_relax_model                  4
% 7.67/1.55  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.55  --bmc1_ucm_layered_model                none
% 7.67/1.55  --bmc1_ucm_max_lemma_size               10
% 7.67/1.55  
% 7.67/1.55  ------ AIG Options
% 7.67/1.55  
% 7.67/1.55  --aig_mode                              false
% 7.67/1.55  
% 7.67/1.55  ------ Instantiation Options
% 7.67/1.55  
% 7.67/1.55  --instantiation_flag                    true
% 7.67/1.55  --inst_sos_flag                         false
% 7.67/1.55  --inst_sos_phase                        true
% 7.67/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.55  --inst_lit_sel_side                     num_symb
% 7.67/1.55  --inst_solver_per_active                1400
% 7.67/1.55  --inst_solver_calls_frac                1.
% 7.67/1.55  --inst_passive_queue_type               priority_queues
% 7.67/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.55  --inst_passive_queues_freq              [25;2]
% 7.67/1.55  --inst_dismatching                      true
% 7.67/1.55  --inst_eager_unprocessed_to_passive     true
% 7.67/1.55  --inst_prop_sim_given                   true
% 7.67/1.55  --inst_prop_sim_new                     false
% 7.67/1.55  --inst_subs_new                         false
% 7.67/1.55  --inst_eq_res_simp                      false
% 7.67/1.55  --inst_subs_given                       false
% 7.67/1.55  --inst_orphan_elimination               true
% 7.67/1.55  --inst_learning_loop_flag               true
% 7.67/1.55  --inst_learning_start                   3000
% 7.67/1.55  --inst_learning_factor                  2
% 7.67/1.55  --inst_start_prop_sim_after_learn       3
% 7.67/1.55  --inst_sel_renew                        solver
% 7.67/1.55  --inst_lit_activity_flag                true
% 7.67/1.55  --inst_restr_to_given                   false
% 7.67/1.55  --inst_activity_threshold               500
% 7.67/1.55  --inst_out_proof                        true
% 7.67/1.55  
% 7.67/1.55  ------ Resolution Options
% 7.67/1.55  
% 7.67/1.55  --resolution_flag                       true
% 7.67/1.55  --res_lit_sel                           adaptive
% 7.67/1.55  --res_lit_sel_side                      none
% 7.67/1.55  --res_ordering                          kbo
% 7.67/1.55  --res_to_prop_solver                    active
% 7.67/1.55  --res_prop_simpl_new                    false
% 7.67/1.55  --res_prop_simpl_given                  true
% 7.67/1.55  --res_passive_queue_type                priority_queues
% 7.67/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.55  --res_passive_queues_freq               [15;5]
% 7.67/1.55  --res_forward_subs                      full
% 7.67/1.55  --res_backward_subs                     full
% 7.67/1.55  --res_forward_subs_resolution           true
% 7.67/1.55  --res_backward_subs_resolution          true
% 7.67/1.55  --res_orphan_elimination                true
% 7.67/1.55  --res_time_limit                        2.
% 7.67/1.55  --res_out_proof                         true
% 7.67/1.55  
% 7.67/1.55  ------ Superposition Options
% 7.67/1.55  
% 7.67/1.55  --superposition_flag                    true
% 7.67/1.55  --sup_passive_queue_type                priority_queues
% 7.67/1.55  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.55  --sup_passive_queues_freq               [1;4]
% 7.67/1.55  --demod_completeness_check              fast
% 7.67/1.55  --demod_use_ground                      true
% 7.67/1.55  --sup_to_prop_solver                    passive
% 7.67/1.55  --sup_prop_simpl_new                    true
% 7.67/1.55  --sup_prop_simpl_given                  true
% 7.67/1.55  --sup_fun_splitting                     false
% 7.67/1.55  --sup_smt_interval                      50000
% 7.67/1.55  
% 7.67/1.55  ------ Superposition Simplification Setup
% 7.67/1.55  
% 7.67/1.55  --sup_indices_passive                   []
% 7.67/1.55  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.55  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.55  --sup_full_bw                           [BwDemod]
% 7.67/1.55  --sup_immed_triv                        [TrivRules]
% 7.67/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.55  --sup_immed_bw_main                     []
% 7.67/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.67/1.55  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.67/1.55  
% 7.67/1.55  ------ Combination Options
% 7.67/1.55  
% 7.67/1.55  --comb_res_mult                         3
% 7.67/1.55  --comb_sup_mult                         2
% 7.67/1.55  --comb_inst_mult                        10
% 7.67/1.55  
% 7.67/1.55  ------ Debug Options
% 7.67/1.55  
% 7.67/1.55  --dbg_backtrace                         false
% 7.67/1.55  --dbg_dump_prop_clauses                 false
% 7.67/1.55  --dbg_dump_prop_clauses_file            -
% 7.67/1.55  --dbg_out_stat                          false
% 7.67/1.55  
% 7.67/1.55  
% 7.67/1.55  
% 7.67/1.55  
% 7.67/1.55  ------ Proving...
% 7.67/1.55  
% 7.67/1.55  
% 7.67/1.55  % SZS status Theorem for theBenchmark.p
% 7.67/1.55  
% 7.67/1.55  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.55  
% 7.67/1.55  fof(f21,conjecture,(
% 7.67/1.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f22,negated_conjecture,(
% 7.67/1.55    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 7.67/1.55    inference(negated_conjecture,[],[f21])).
% 7.67/1.55  
% 7.67/1.55  fof(f32,plain,(
% 7.67/1.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 7.67/1.55    inference(ennf_transformation,[],[f22])).
% 7.67/1.55  
% 7.67/1.55  fof(f37,plain,(
% 7.67/1.55    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 7.67/1.55    introduced(choice_axiom,[])).
% 7.67/1.55  
% 7.67/1.55  fof(f38,plain,(
% 7.67/1.55    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 7.67/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f37])).
% 7.67/1.55  
% 7.67/1.55  fof(f64,plain,(
% 7.67/1.55    v1_relat_1(sK0)),
% 7.67/1.55    inference(cnf_transformation,[],[f38])).
% 7.67/1.55  
% 7.67/1.55  fof(f13,axiom,(
% 7.67/1.55    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f24,plain,(
% 7.67/1.55    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.67/1.55    inference(ennf_transformation,[],[f13])).
% 7.67/1.55  
% 7.67/1.55  fof(f55,plain,(
% 7.67/1.55    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f24])).
% 7.67/1.55  
% 7.67/1.55  fof(f1,axiom,(
% 7.67/1.55    v1_xboole_0(k1_xboole_0)),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f39,plain,(
% 7.67/1.55    v1_xboole_0(k1_xboole_0)),
% 7.67/1.55    inference(cnf_transformation,[],[f1])).
% 7.67/1.55  
% 7.67/1.55  fof(f12,axiom,(
% 7.67/1.55    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f23,plain,(
% 7.67/1.55    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 7.67/1.55    inference(ennf_transformation,[],[f12])).
% 7.67/1.55  
% 7.67/1.55  fof(f54,plain,(
% 7.67/1.55    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f23])).
% 7.67/1.55  
% 7.67/1.55  fof(f19,axiom,(
% 7.67/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f31,plain,(
% 7.67/1.55    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.67/1.55    inference(ennf_transformation,[],[f19])).
% 7.67/1.55  
% 7.67/1.55  fof(f61,plain,(
% 7.67/1.55    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f31])).
% 7.67/1.55  
% 7.67/1.55  fof(f17,axiom,(
% 7.67/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f29,plain,(
% 7.67/1.55    ! [X0] : (! [X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.67/1.55    inference(ennf_transformation,[],[f17])).
% 7.67/1.55  
% 7.67/1.55  fof(f59,plain,(
% 7.67/1.55    ( ! [X0,X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f29])).
% 7.67/1.55  
% 7.67/1.55  fof(f3,axiom,(
% 7.67/1.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f43,plain,(
% 7.67/1.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f3])).
% 7.67/1.55  
% 7.67/1.55  fof(f6,axiom,(
% 7.67/1.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f46,plain,(
% 7.67/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.67/1.55    inference(cnf_transformation,[],[f6])).
% 7.67/1.55  
% 7.67/1.55  fof(f10,axiom,(
% 7.67/1.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f52,plain,(
% 7.67/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f10])).
% 7.67/1.55  
% 7.67/1.55  fof(f66,plain,(
% 7.67/1.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 7.67/1.55    inference(definition_unfolding,[],[f46,f52,f52])).
% 7.67/1.55  
% 7.67/1.55  fof(f68,plain,(
% 7.67/1.55    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 7.67/1.55    inference(definition_unfolding,[],[f43,f66])).
% 7.67/1.55  
% 7.67/1.55  fof(f5,axiom,(
% 7.67/1.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f45,plain,(
% 7.67/1.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.67/1.55    inference(cnf_transformation,[],[f5])).
% 7.67/1.55  
% 7.67/1.55  fof(f69,plain,(
% 7.67/1.55    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 7.67/1.55    inference(definition_unfolding,[],[f45,f52])).
% 7.67/1.55  
% 7.67/1.55  fof(f15,axiom,(
% 7.67/1.55    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f27,plain,(
% 7.67/1.55    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 7.67/1.55    inference(ennf_transformation,[],[f15])).
% 7.67/1.55  
% 7.67/1.55  fof(f57,plain,(
% 7.67/1.55    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f27])).
% 7.67/1.55  
% 7.67/1.55  fof(f14,axiom,(
% 7.67/1.55    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f25,plain,(
% 7.67/1.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.67/1.55    inference(ennf_transformation,[],[f14])).
% 7.67/1.55  
% 7.67/1.55  fof(f26,plain,(
% 7.67/1.55    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.67/1.55    inference(flattening,[],[f25])).
% 7.67/1.55  
% 7.67/1.55  fof(f56,plain,(
% 7.67/1.55    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f26])).
% 7.67/1.55  
% 7.67/1.55  fof(f16,axiom,(
% 7.67/1.55    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f28,plain,(
% 7.67/1.55    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.67/1.55    inference(ennf_transformation,[],[f16])).
% 7.67/1.55  
% 7.67/1.55  fof(f58,plain,(
% 7.67/1.55    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f28])).
% 7.67/1.55  
% 7.67/1.55  fof(f71,plain,(
% 7.67/1.55    ( ! [X0] : (k6_subset_1(X0,k6_subset_1(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 7.67/1.55    inference(definition_unfolding,[],[f58,f66])).
% 7.67/1.55  
% 7.67/1.55  fof(f20,axiom,(
% 7.67/1.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f62,plain,(
% 7.67/1.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.67/1.55    inference(cnf_transformation,[],[f20])).
% 7.67/1.55  
% 7.67/1.55  fof(f18,axiom,(
% 7.67/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f30,plain,(
% 7.67/1.55    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.67/1.55    inference(ennf_transformation,[],[f18])).
% 7.67/1.55  
% 7.67/1.55  fof(f60,plain,(
% 7.67/1.55    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f30])).
% 7.67/1.55  
% 7.67/1.55  fof(f4,axiom,(
% 7.67/1.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f44,plain,(
% 7.67/1.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f4])).
% 7.67/1.55  
% 7.67/1.55  fof(f2,axiom,(
% 7.67/1.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f33,plain,(
% 7.67/1.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.67/1.55    inference(nnf_transformation,[],[f2])).
% 7.67/1.55  
% 7.67/1.55  fof(f34,plain,(
% 7.67/1.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.67/1.55    inference(flattening,[],[f33])).
% 7.67/1.55  
% 7.67/1.55  fof(f42,plain,(
% 7.67/1.55    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f34])).
% 7.67/1.55  
% 7.67/1.55  fof(f9,axiom,(
% 7.67/1.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.67/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.55  
% 7.67/1.55  fof(f35,plain,(
% 7.67/1.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.67/1.55    inference(nnf_transformation,[],[f9])).
% 7.67/1.55  
% 7.67/1.55  fof(f36,plain,(
% 7.67/1.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.67/1.55    inference(flattening,[],[f35])).
% 7.67/1.55  
% 7.67/1.55  fof(f50,plain,(
% 7.67/1.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.67/1.55    inference(cnf_transformation,[],[f36])).
% 7.67/1.55  
% 7.67/1.55  fof(f75,plain,(
% 7.67/1.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.67/1.55    inference(equality_resolution,[],[f50])).
% 7.67/1.55  
% 7.67/1.55  fof(f49,plain,(
% 7.67/1.55    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.67/1.55    inference(cnf_transformation,[],[f36])).
% 7.67/1.55  
% 7.67/1.55  fof(f65,plain,(
% 7.67/1.55    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 7.67/1.55    inference(cnf_transformation,[],[f38])).
% 7.67/1.55  
% 7.67/1.55  cnf(c_22,negated_conjecture,
% 7.67/1.55      ( v1_relat_1(sK0) ),
% 7.67/1.55      inference(cnf_transformation,[],[f64]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_453,plain,
% 7.67/1.55      ( v1_relat_1(sK0) = iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_12,plain,
% 7.67/1.55      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 7.67/1.55      inference(cnf_transformation,[],[f55]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_460,plain,
% 7.67/1.55      ( v1_relat_1(X0) != iProver_top
% 7.67/1.55      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_0,plain,
% 7.67/1.55      ( v1_xboole_0(k1_xboole_0) ),
% 7.67/1.55      inference(cnf_transformation,[],[f39]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_465,plain,
% 7.67/1.55      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_11,plain,
% 7.67/1.55      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 7.67/1.55      inference(cnf_transformation,[],[f54]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_461,plain,
% 7.67/1.55      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1178,plain,
% 7.67/1.55      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_465,c_461]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_18,plain,
% 7.67/1.55      ( ~ v1_relat_1(X0)
% 7.67/1.55      | ~ v1_relat_1(X1)
% 7.67/1.55      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 7.67/1.55      inference(cnf_transformation,[],[f61]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_454,plain,
% 7.67/1.55      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 7.67/1.55      | v1_relat_1(X1) != iProver_top
% 7.67/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1635,plain,
% 7.67/1.55      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 7.67/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_1178,c_454]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_16,plain,
% 7.67/1.55      ( ~ v1_relat_1(X0)
% 7.67/1.55      | ~ v1_relat_1(X1)
% 7.67/1.55      | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
% 7.67/1.55      inference(cnf_transformation,[],[f59]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_456,plain,
% 7.67/1.55      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
% 7.67/1.55      | v1_relat_1(X0) != iProver_top
% 7.67/1.55      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1082,plain,
% 7.67/1.55      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
% 7.67/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_453,c_456]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_2086,plain,
% 7.67/1.55      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_453,c_1082]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4,plain,
% 7.67/1.55      ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.67/1.55      inference(cnf_transformation,[],[f68]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_6,plain,
% 7.67/1.55      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 7.67/1.55      inference(cnf_transformation,[],[f69]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_484,plain,
% 7.67/1.55      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 7.67/1.55      inference(light_normalisation,[status(thm)],[c_4,c_6]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_2092,plain,
% 7.67/1.55      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.67/1.55      inference(demodulation,[status(thm)],[c_2086,c_484]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_2863,plain,
% 7.67/1.55      ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 7.67/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(light_normalisation,[status(thm)],[c_1635,c_2092]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_2869,plain,
% 7.67/1.55      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
% 7.67/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_460,c_2863]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_3282,plain,
% 7.67/1.55      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_453,c_2869]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_14,plain,
% 7.67/1.55      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 7.67/1.55      inference(cnf_transformation,[],[f57]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_458,plain,
% 7.67/1.55      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1183,plain,
% 7.67/1.55      ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_453,c_458]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_3292,plain,
% 7.67/1.55      ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,sK0) ),
% 7.67/1.55      inference(light_normalisation,[status(thm)],[c_3282,c_1183]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_24758,plain,
% 7.67/1.55      ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) != iProver_top
% 7.67/1.55      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_3292,c_460]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_23,plain,
% 7.67/1.55      ( v1_relat_1(sK0) = iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_45,plain,
% 7.67/1.55      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_47,plain,
% 7.67/1.55      ( v1_relat_1(k1_xboole_0) = iProver_top
% 7.67/1.55      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.67/1.55      inference(instantiation,[status(thm)],[c_45]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_61,plain,
% 7.67/1.55      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_13,plain,
% 7.67/1.55      ( ~ v1_relat_1(X0)
% 7.67/1.55      | ~ v1_relat_1(X1)
% 7.67/1.55      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 7.67/1.55      inference(cnf_transformation,[],[f56]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1140,plain,
% 7.67/1.55      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 7.67/1.55      | ~ v1_relat_1(sK0)
% 7.67/1.55      | ~ v1_relat_1(k1_xboole_0) ),
% 7.67/1.55      inference(instantiation,[status(thm)],[c_13]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1141,plain,
% 7.67/1.55      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 7.67/1.55      | v1_relat_1(sK0) != iProver_top
% 7.67/1.55      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_1140]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_24761,plain,
% 7.67/1.55      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 7.67/1.55      inference(global_propositional_subsumption,
% 7.67/1.55                [status(thm)],
% 7.67/1.55                [c_24758,c_23,c_47,c_61,c_1141]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_15,plain,
% 7.67/1.55      ( ~ v1_relat_1(X0)
% 7.67/1.55      | k6_subset_1(X0,k6_subset_1(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 7.67/1.55      inference(cnf_transformation,[],[f71]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_457,plain,
% 7.67/1.55      ( k6_subset_1(X0,k6_subset_1(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 7.67/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_24896,plain,
% 7.67/1.55      ( k6_subset_1(k5_relat_1(k1_xboole_0,sK0),k6_subset_1(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_24761,c_457]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_20,plain,
% 7.67/1.55      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.67/1.55      inference(cnf_transformation,[],[f62]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_17,plain,
% 7.67/1.55      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 7.67/1.55      | ~ v1_relat_1(X0)
% 7.67/1.55      | ~ v1_relat_1(X1) ),
% 7.67/1.55      inference(cnf_transformation,[],[f60]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_455,plain,
% 7.67/1.55      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 7.67/1.55      | v1_relat_1(X0) != iProver_top
% 7.67/1.55      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_859,plain,
% 7.67/1.55      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 7.67/1.55      | v1_relat_1(X0) != iProver_top
% 7.67/1.55      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_20,c_455]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1620,plain,
% 7.67/1.55      ( v1_relat_1(X0) != iProver_top
% 7.67/1.55      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 7.67/1.55      inference(global_propositional_subsumption,
% 7.67/1.55                [status(thm)],
% 7.67/1.55                [c_859,c_47,c_61]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1621,plain,
% 7.67/1.55      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 7.67/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(renaming,[status(thm)],[c_1620]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_5,plain,
% 7.67/1.55      ( r1_tarski(k1_xboole_0,X0) ),
% 7.67/1.55      inference(cnf_transformation,[],[f44]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_462,plain,
% 7.67/1.55      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1,plain,
% 7.67/1.55      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.67/1.55      inference(cnf_transformation,[],[f42]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_464,plain,
% 7.67/1.55      ( X0 = X1
% 7.67/1.55      | r1_tarski(X0,X1) != iProver_top
% 7.67/1.55      | r1_tarski(X1,X0) != iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1443,plain,
% 7.67/1.55      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_462,c_464]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1930,plain,
% 7.67/1.55      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 7.67/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_1621,c_1443]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_8270,plain,
% 7.67/1.55      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_453,c_1930]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_24911,plain,
% 7.67/1.55      ( k6_subset_1(k5_relat_1(k1_xboole_0,sK0),k6_subset_1(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 7.67/1.55      inference(light_normalisation,[status(thm)],[c_24896,c_8270]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_8,plain,
% 7.67/1.55      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.67/1.55      inference(cnf_transformation,[],[f75]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_24912,plain,
% 7.67/1.55      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 7.67/1.55      inference(demodulation,[status(thm)],[c_24911,c_6,c_8,c_484]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_217,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_12716,plain,
% 7.67/1.55      ( k5_relat_1(sK0,k1_xboole_0) != X0
% 7.67/1.55      | k1_xboole_0 != X0
% 7.67/1.55      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
% 7.67/1.55      inference(instantiation,[status(thm)],[c_217]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_12717,plain,
% 7.67/1.55      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 7.67/1.55      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
% 7.67/1.55      | k1_xboole_0 != k1_xboole_0 ),
% 7.67/1.55      inference(instantiation,[status(thm)],[c_12716]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_459,plain,
% 7.67/1.55      ( v1_relat_1(X0) != iProver_top
% 7.67/1.55      | v1_relat_1(X1) != iProver_top
% 7.67/1.55      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 7.67/1.55      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1466,plain,
% 7.67/1.55      ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
% 7.67/1.55      | v1_relat_1(X0) != iProver_top
% 7.67/1.55      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_459,c_458]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4975,plain,
% 7.67/1.55      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
% 7.67/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_453,c_1466]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_5258,plain,
% 7.67/1.55      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_1178,c_4975]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_2871,plain,
% 7.67/1.55      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_453,c_2863]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_2901,plain,
% 7.67/1.55      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 7.67/1.55      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 7.67/1.55      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_2871,c_459]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4689,plain,
% 7.67/1.55      ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 7.67/1.55      | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 7.67/1.55      inference(global_propositional_subsumption,
% 7.67/1.55                [status(thm)],
% 7.67/1.55                [c_2901,c_47,c_61]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4690,plain,
% 7.67/1.55      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 7.67/1.55      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.67/1.55      inference(renaming,[status(thm)],[c_4689]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4710,plain,
% 7.67/1.55      ( k6_subset_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k6_subset_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 7.67/1.55      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_4690,c_457]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_1444,plain,
% 7.67/1.55      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 7.67/1.55      | r1_tarski(k1_relat_1(X0),k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 7.67/1.55      | v1_relat_1(X0) != iProver_top
% 7.67/1.55      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_455,c_464]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4023,plain,
% 7.67/1.55      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_relat_1(k1_xboole_0)
% 7.67/1.55      | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 7.67/1.55      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 7.67/1.55      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_2871,c_1444]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4028,plain,
% 7.67/1.55      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 7.67/1.55      | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 7.67/1.55      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 7.67/1.55      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.67/1.55      inference(light_normalisation,[status(thm)],[c_4023,c_20,c_2871]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4044,plain,
% 7.67/1.55      ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 7.67/1.55      | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 7.67/1.55      | k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 7.67/1.55      inference(global_propositional_subsumption,
% 7.67/1.55                [status(thm)],
% 7.67/1.55                [c_4028,c_47,c_61]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4045,plain,
% 7.67/1.55      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 7.67/1.55      | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 7.67/1.55      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.67/1.55      inference(renaming,[status(thm)],[c_4044]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4051,plain,
% 7.67/1.55      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 7.67/1.55      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.67/1.55      inference(forward_subsumption_resolution,
% 7.67/1.55                [status(thm)],
% 7.67/1.55                [c_4045,c_462]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4053,plain,
% 7.67/1.55      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 7.67/1.55      | v1_relat_1(sK0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_460,c_4051]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4299,plain,
% 7.67/1.55      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 7.67/1.55      inference(global_propositional_subsumption,
% 7.67/1.55                [status(thm)],
% 7.67/1.55                [c_4053,c_23]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4732,plain,
% 7.67/1.55      ( k6_subset_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k6_subset_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 7.67/1.55      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.67/1.55      inference(light_normalisation,[status(thm)],[c_4710,c_4299]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4733,plain,
% 7.67/1.55      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
% 7.67/1.55      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 7.67/1.55      inference(demodulation,[status(thm)],[c_4732,c_6,c_8,c_484]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_4967,plain,
% 7.67/1.55      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
% 7.67/1.55      | v1_relat_1(sK0) != iProver_top ),
% 7.67/1.55      inference(superposition,[status(thm)],[c_460,c_4733]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_5243,plain,
% 7.67/1.55      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 7.67/1.55      inference(global_propositional_subsumption,
% 7.67/1.55                [status(thm)],
% 7.67/1.55                [c_4967,c_23]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_5265,plain,
% 7.67/1.55      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 7.67/1.55      inference(light_normalisation,[status(thm)],[c_5258,c_2092,c_5243]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_615,plain,
% 7.67/1.55      ( k5_relat_1(k1_xboole_0,sK0) != X0
% 7.67/1.55      | k1_xboole_0 != X0
% 7.67/1.55      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
% 7.67/1.55      inference(instantiation,[status(thm)],[c_217]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_616,plain,
% 7.67/1.55      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 7.67/1.55      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
% 7.67/1.55      | k1_xboole_0 != k1_xboole_0 ),
% 7.67/1.55      inference(instantiation,[status(thm)],[c_615]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_50,plain,
% 7.67/1.55      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.67/1.55      inference(instantiation,[status(thm)],[c_8]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_9,plain,
% 7.67/1.55      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.67/1.55      | k1_xboole_0 = X1
% 7.67/1.55      | k1_xboole_0 = X0 ),
% 7.67/1.55      inference(cnf_transformation,[],[f49]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_49,plain,
% 7.67/1.55      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.67/1.55      | k1_xboole_0 = k1_xboole_0 ),
% 7.67/1.55      inference(instantiation,[status(thm)],[c_9]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(c_21,negated_conjecture,
% 7.67/1.55      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 7.67/1.55      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 7.67/1.55      inference(cnf_transformation,[],[f65]) ).
% 7.67/1.55  
% 7.67/1.55  cnf(contradiction,plain,
% 7.67/1.55      ( $false ),
% 7.67/1.55      inference(minisat,
% 7.67/1.55                [status(thm)],
% 7.67/1.55                [c_24912,c_12717,c_5265,c_616,c_50,c_49,c_21]) ).
% 7.67/1.55  
% 7.67/1.55  
% 7.67/1.55  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.55  
% 7.67/1.55  ------                               Statistics
% 7.67/1.55  
% 7.67/1.55  ------ Selected
% 7.67/1.55  
% 7.67/1.55  total_time:                             0.875
% 7.67/1.55  
%------------------------------------------------------------------------------
