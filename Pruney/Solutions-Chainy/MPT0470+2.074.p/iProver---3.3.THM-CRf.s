%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:08 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 285 expanded)
%              Number of clauses        :   73 ( 121 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  267 ( 520 expanded)
%              Number of equality atoms :  154 ( 297 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f31,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f52,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f59,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f57])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_115,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_361,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_129,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_351,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_129])).

cnf(c_6,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_123,plain,
    ( v1_relat_1(X0_39)
    | ~ v1_xboole_0(X0_39) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_356,plain,
    ( v1_relat_1(X0_39) = iProver_top
    | v1_xboole_0(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_123])).

cnf(c_639,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_351,c_356])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_122,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | v1_relat_1(k5_relat_1(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_357,plain,
    ( v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(k5_relat_1(X1_39,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_122])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_121,plain,
    ( ~ v1_relat_1(X0_39)
    | k1_setfam_1(k4_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,k2_zfmisc_1(k1_relat_1(X0_39),k2_relat_1(X0_39)))) = X0_39 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_358,plain,
    ( k1_setfam_1(k4_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,k2_zfmisc_1(k1_relat_1(X0_39),k2_relat_1(X0_39)))) = X0_39
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_121])).

cnf(c_867,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0_39,X1_39),k5_relat_1(X0_39,X1_39),k5_relat_1(X0_39,X1_39),k5_relat_1(X0_39,X1_39),k5_relat_1(X0_39,X1_39),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0_39,X1_39)),k2_relat_1(k5_relat_1(X0_39,X1_39))))) = k5_relat_1(X0_39,X1_39)
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_358])).

cnf(c_2520,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,X0_39),k5_relat_1(k1_xboole_0,X0_39),k5_relat_1(k1_xboole_0,X0_39),k5_relat_1(k1_xboole_0,X0_39),k5_relat_1(k1_xboole_0,X0_39),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)),k2_relat_1(k5_relat_1(k1_xboole_0,X0_39))))) = k5_relat_1(k1_xboole_0,X0_39)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_867])).

cnf(c_12789,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_361,c_2520])).

cnf(c_11,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_118,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_120,plain,
    ( ~ r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39))
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | k1_relat_1(k5_relat_1(X0_39,X1_39)) = k1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_359,plain,
    ( k1_relat_1(k5_relat_1(X0_39,X1_39)) = k1_relat_1(X0_39)
    | r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(X1_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_120])).

cnf(c_884,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_118,c_359])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_117,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_898,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_884,c_117])).

cnf(c_28,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_30,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_42,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_974,plain,
    ( v1_relat_1(X0_39) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0_39)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_898,c_30,c_42])).

cnf(c_975,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(renaming,[status(thm)],[c_974])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_126,plain,
    ( r1_tarski(k1_xboole_0,X0_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_353,plain,
    ( r1_tarski(k1_xboole_0,X0_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_126])).

cnf(c_981,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_xboole_0
    | v1_relat_1(X0_39) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_975,c_353])).

cnf(c_985,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_361,c_981])).

cnf(c_12813,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_12789,c_985])).

cnf(c_2,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_127,plain,
    ( k1_setfam_1(k4_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,k1_xboole_0)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_124,plain,
    ( ~ v1_xboole_0(X0_39)
    | v1_xboole_0(k2_zfmisc_1(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_355,plain,
    ( v1_xboole_0(X0_39) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0_39,X1_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_128,plain,
    ( ~ v1_xboole_0(X0_39)
    | k1_xboole_0 = X0_39 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_352,plain,
    ( k1_xboole_0 = X0_39
    | v1_xboole_0(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_128])).

cnf(c_770,plain,
    ( k2_zfmisc_1(X0_39,X1_39) = k1_xboole_0
    | v1_xboole_0(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_355,c_352])).

cnf(c_1970,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0_39) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_351,c_770])).

cnf(c_12814,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12813,c_127,c_1970])).

cnf(c_2519,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,X0_39),k5_relat_1(sK0,X0_39),k5_relat_1(sK0,X0_39),k5_relat_1(sK0,X0_39),k5_relat_1(sK0,X0_39),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0_39)),k2_relat_1(k5_relat_1(sK0,X0_39))))) = k5_relat_1(sK0,X0_39)
    | v1_relat_1(X0_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_361,c_867])).

cnf(c_12192,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_639,c_2519])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_119,plain,
    ( ~ r1_tarski(k1_relat_1(X0_39),k2_relat_1(X1_39))
    | ~ v1_relat_1(X1_39)
    | ~ v1_relat_1(X0_39)
    | k2_relat_1(k5_relat_1(X1_39,X0_39)) = k2_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_360,plain,
    ( k2_relat_1(k5_relat_1(X0_39,X1_39)) = k2_relat_1(X1_39)
    | r1_tarski(k1_relat_1(X1_39),k2_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X1_39) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_119])).

cnf(c_1003,plain,
    ( k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k2_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_117,c_360])).

cnf(c_1017,plain,
    ( k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1003,c_118])).

cnf(c_1112,plain,
    ( v1_relat_1(X0_39) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(X0_39)) != iProver_top
    | k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1017,c_30,c_42])).

cnf(c_1113,plain,
    ( k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(X0_39)) != iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(renaming,[status(thm)],[c_1112])).

cnf(c_1119,plain,
    ( k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0_39) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1113,c_353])).

cnf(c_1123,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_361,c_1119])).

cnf(c_12211,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_12192,c_1123])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_125,plain,
    ( ~ v1_xboole_0(X0_39)
    | v1_xboole_0(k2_zfmisc_1(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_354,plain,
    ( v1_xboole_0(X0_39) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1_39,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_645,plain,
    ( k2_zfmisc_1(X0_39,X1_39) = k1_xboole_0
    | v1_xboole_0(X1_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_354,c_352])).

cnf(c_1614,plain,
    ( k2_zfmisc_1(X0_39,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_351,c_645])).

cnf(c_12212,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12211,c_127,c_1614])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_116,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_12475,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12212,c_116])).

cnf(c_12476,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_12475])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12814,c_12476])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.48/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.00  
% 3.48/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/1.00  
% 3.48/1.00  ------  iProver source info
% 3.48/1.00  
% 3.48/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.48/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/1.00  git: non_committed_changes: false
% 3.48/1.00  git: last_make_outside_of_git: false
% 3.48/1.00  
% 3.48/1.00  ------ 
% 3.48/1.00  
% 3.48/1.00  ------ Input Options
% 3.48/1.00  
% 3.48/1.00  --out_options                           all
% 3.48/1.00  --tptp_safe_out                         true
% 3.48/1.00  --problem_path                          ""
% 3.48/1.00  --include_path                          ""
% 3.48/1.00  --clausifier                            res/vclausify_rel
% 3.48/1.00  --clausifier_options                    --mode clausify
% 3.48/1.00  --stdin                                 false
% 3.48/1.00  --stats_out                             sel
% 3.48/1.00  
% 3.48/1.00  ------ General Options
% 3.48/1.00  
% 3.48/1.00  --fof                                   false
% 3.48/1.00  --time_out_real                         604.99
% 3.48/1.00  --time_out_virtual                      -1.
% 3.48/1.00  --symbol_type_check                     false
% 3.48/1.00  --clausify_out                          false
% 3.48/1.00  --sig_cnt_out                           false
% 3.48/1.00  --trig_cnt_out                          false
% 3.48/1.00  --trig_cnt_out_tolerance                1.
% 3.48/1.00  --trig_cnt_out_sk_spl                   false
% 3.48/1.00  --abstr_cl_out                          false
% 3.48/1.00  
% 3.48/1.00  ------ Global Options
% 3.48/1.00  
% 3.48/1.00  --schedule                              none
% 3.48/1.00  --add_important_lit                     false
% 3.48/1.00  --prop_solver_per_cl                    1000
% 3.48/1.00  --min_unsat_core                        false
% 3.48/1.00  --soft_assumptions                      false
% 3.48/1.00  --soft_lemma_size                       3
% 3.48/1.00  --prop_impl_unit_size                   0
% 3.48/1.00  --prop_impl_unit                        []
% 3.48/1.00  --share_sel_clauses                     true
% 3.48/1.00  --reset_solvers                         false
% 3.48/1.00  --bc_imp_inh                            [conj_cone]
% 3.48/1.00  --conj_cone_tolerance                   3.
% 3.48/1.00  --extra_neg_conj                        none
% 3.48/1.00  --large_theory_mode                     true
% 3.48/1.00  --prolific_symb_bound                   200
% 3.48/1.00  --lt_threshold                          2000
% 3.48/1.00  --clause_weak_htbl                      true
% 3.48/1.00  --gc_record_bc_elim                     false
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing Options
% 3.48/1.00  
% 3.48/1.00  --preprocessing_flag                    true
% 3.48/1.00  --time_out_prep_mult                    0.1
% 3.48/1.00  --splitting_mode                        input
% 3.48/1.00  --splitting_grd                         true
% 3.48/1.00  --splitting_cvd                         false
% 3.48/1.00  --splitting_cvd_svl                     false
% 3.48/1.00  --splitting_nvd                         32
% 3.48/1.00  --sub_typing                            true
% 3.48/1.00  --prep_gs_sim                           false
% 3.48/1.00  --prep_unflatten                        true
% 3.48/1.00  --prep_res_sim                          true
% 3.48/1.00  --prep_upred                            true
% 3.48/1.00  --prep_sem_filter                       exhaustive
% 3.48/1.00  --prep_sem_filter_out                   false
% 3.48/1.00  --pred_elim                             false
% 3.48/1.00  --res_sim_input                         true
% 3.48/1.00  --eq_ax_congr_red                       true
% 3.48/1.00  --pure_diseq_elim                       true
% 3.48/1.00  --brand_transform                       false
% 3.48/1.00  --non_eq_to_eq                          false
% 3.48/1.00  --prep_def_merge                        true
% 3.48/1.00  --prep_def_merge_prop_impl              false
% 3.48/1.00  --prep_def_merge_mbd                    true
% 3.48/1.00  --prep_def_merge_tr_red                 false
% 3.48/1.00  --prep_def_merge_tr_cl                  false
% 3.48/1.00  --smt_preprocessing                     true
% 3.48/1.00  --smt_ac_axioms                         fast
% 3.48/1.00  --preprocessed_out                      false
% 3.48/1.00  --preprocessed_stats                    false
% 3.48/1.00  
% 3.48/1.00  ------ Abstraction refinement Options
% 3.48/1.00  
% 3.48/1.00  --abstr_ref                             []
% 3.48/1.00  --abstr_ref_prep                        false
% 3.48/1.00  --abstr_ref_until_sat                   false
% 3.48/1.00  --abstr_ref_sig_restrict                funpre
% 3.48/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/1.00  --abstr_ref_under                       []
% 3.48/1.00  
% 3.48/1.00  ------ SAT Options
% 3.48/1.00  
% 3.48/1.00  --sat_mode                              false
% 3.48/1.00  --sat_fm_restart_options                ""
% 3.48/1.00  --sat_gr_def                            false
% 3.48/1.00  --sat_epr_types                         true
% 3.48/1.00  --sat_non_cyclic_types                  false
% 3.48/1.00  --sat_finite_models                     false
% 3.48/1.00  --sat_fm_lemmas                         false
% 3.48/1.00  --sat_fm_prep                           false
% 3.48/1.00  --sat_fm_uc_incr                        true
% 3.48/1.00  --sat_out_model                         small
% 3.48/1.00  --sat_out_clauses                       false
% 3.48/1.00  
% 3.48/1.00  ------ QBF Options
% 3.48/1.00  
% 3.48/1.00  --qbf_mode                              false
% 3.48/1.00  --qbf_elim_univ                         false
% 3.48/1.00  --qbf_dom_inst                          none
% 3.48/1.00  --qbf_dom_pre_inst                      false
% 3.48/1.00  --qbf_sk_in                             false
% 3.48/1.00  --qbf_pred_elim                         true
% 3.48/1.00  --qbf_split                             512
% 3.48/1.00  
% 3.48/1.00  ------ BMC1 Options
% 3.48/1.00  
% 3.48/1.00  --bmc1_incremental                      false
% 3.48/1.00  --bmc1_axioms                           reachable_all
% 3.48/1.00  --bmc1_min_bound                        0
% 3.48/1.00  --bmc1_max_bound                        -1
% 3.48/1.00  --bmc1_max_bound_default                -1
% 3.48/1.00  --bmc1_symbol_reachability              true
% 3.48/1.00  --bmc1_property_lemmas                  false
% 3.48/1.00  --bmc1_k_induction                      false
% 3.48/1.00  --bmc1_non_equiv_states                 false
% 3.48/1.00  --bmc1_deadlock                         false
% 3.48/1.00  --bmc1_ucm                              false
% 3.48/1.00  --bmc1_add_unsat_core                   none
% 3.48/1.00  --bmc1_unsat_core_children              false
% 3.48/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/1.00  --bmc1_out_stat                         full
% 3.48/1.00  --bmc1_ground_init                      false
% 3.48/1.00  --bmc1_pre_inst_next_state              false
% 3.48/1.00  --bmc1_pre_inst_state                   false
% 3.48/1.00  --bmc1_pre_inst_reach_state             false
% 3.48/1.00  --bmc1_out_unsat_core                   false
% 3.48/1.00  --bmc1_aig_witness_out                  false
% 3.48/1.00  --bmc1_verbose                          false
% 3.48/1.00  --bmc1_dump_clauses_tptp                false
% 3.48/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.48/1.00  --bmc1_dump_file                        -
% 3.48/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.48/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.48/1.00  --bmc1_ucm_extend_mode                  1
% 3.48/1.00  --bmc1_ucm_init_mode                    2
% 3.48/1.00  --bmc1_ucm_cone_mode                    none
% 3.48/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.48/1.00  --bmc1_ucm_relax_model                  4
% 3.48/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.48/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/1.00  --bmc1_ucm_layered_model                none
% 3.48/1.00  --bmc1_ucm_max_lemma_size               10
% 3.48/1.00  
% 3.48/1.00  ------ AIG Options
% 3.48/1.00  
% 3.48/1.00  --aig_mode                              false
% 3.48/1.00  
% 3.48/1.00  ------ Instantiation Options
% 3.48/1.00  
% 3.48/1.00  --instantiation_flag                    true
% 3.48/1.00  --inst_sos_flag                         false
% 3.48/1.00  --inst_sos_phase                        true
% 3.48/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/1.00  --inst_lit_sel_side                     num_symb
% 3.48/1.00  --inst_solver_per_active                1400
% 3.48/1.00  --inst_solver_calls_frac                1.
% 3.48/1.00  --inst_passive_queue_type               priority_queues
% 3.48/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/1.00  --inst_passive_queues_freq              [25;2]
% 3.48/1.00  --inst_dismatching                      true
% 3.48/1.00  --inst_eager_unprocessed_to_passive     true
% 3.48/1.00  --inst_prop_sim_given                   true
% 3.48/1.00  --inst_prop_sim_new                     false
% 3.48/1.00  --inst_subs_new                         false
% 3.48/1.00  --inst_eq_res_simp                      false
% 3.48/1.00  --inst_subs_given                       false
% 3.48/1.00  --inst_orphan_elimination               true
% 3.48/1.00  --inst_learning_loop_flag               true
% 3.48/1.00  --inst_learning_start                   3000
% 3.48/1.00  --inst_learning_factor                  2
% 3.48/1.00  --inst_start_prop_sim_after_learn       3
% 3.48/1.00  --inst_sel_renew                        solver
% 3.48/1.00  --inst_lit_activity_flag                true
% 3.48/1.00  --inst_restr_to_given                   false
% 3.48/1.00  --inst_activity_threshold               500
% 3.48/1.00  --inst_out_proof                        true
% 3.48/1.00  
% 3.48/1.00  ------ Resolution Options
% 3.48/1.00  
% 3.48/1.00  --resolution_flag                       true
% 3.48/1.00  --res_lit_sel                           adaptive
% 3.48/1.00  --res_lit_sel_side                      none
% 3.48/1.00  --res_ordering                          kbo
% 3.48/1.00  --res_to_prop_solver                    active
% 3.48/1.00  --res_prop_simpl_new                    false
% 3.48/1.00  --res_prop_simpl_given                  true
% 3.48/1.00  --res_passive_queue_type                priority_queues
% 3.48/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/1.00  --res_passive_queues_freq               [15;5]
% 3.48/1.00  --res_forward_subs                      full
% 3.48/1.00  --res_backward_subs                     full
% 3.48/1.00  --res_forward_subs_resolution           true
% 3.48/1.00  --res_backward_subs_resolution          true
% 3.48/1.00  --res_orphan_elimination                true
% 3.48/1.00  --res_time_limit                        2.
% 3.48/1.00  --res_out_proof                         true
% 3.48/1.00  
% 3.48/1.00  ------ Superposition Options
% 3.48/1.00  
% 3.48/1.00  --superposition_flag                    true
% 3.48/1.00  --sup_passive_queue_type                priority_queues
% 3.48/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/1.00  --sup_passive_queues_freq               [1;4]
% 3.48/1.00  --demod_completeness_check              fast
% 3.48/1.00  --demod_use_ground                      true
% 3.48/1.00  --sup_to_prop_solver                    passive
% 3.48/1.00  --sup_prop_simpl_new                    true
% 3.48/1.00  --sup_prop_simpl_given                  true
% 3.48/1.00  --sup_fun_splitting                     false
% 3.48/1.00  --sup_smt_interval                      50000
% 3.48/1.00  
% 3.48/1.00  ------ Superposition Simplification Setup
% 3.48/1.00  
% 3.48/1.00  --sup_indices_passive                   []
% 3.48/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.00  --sup_full_bw                           [BwDemod]
% 3.48/1.00  --sup_immed_triv                        [TrivRules]
% 3.48/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.00  --sup_immed_bw_main                     []
% 3.48/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.00  
% 3.48/1.00  ------ Combination Options
% 3.48/1.00  
% 3.48/1.00  --comb_res_mult                         3
% 3.48/1.00  --comb_sup_mult                         2
% 3.48/1.00  --comb_inst_mult                        10
% 3.48/1.00  
% 3.48/1.00  ------ Debug Options
% 3.48/1.00  
% 3.48/1.00  --dbg_backtrace                         false
% 3.48/1.00  --dbg_dump_prop_clauses                 false
% 3.48/1.00  --dbg_dump_prop_clauses_file            -
% 3.48/1.00  --dbg_out_stat                          false
% 3.48/1.00  ------ Parsing...
% 3.48/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/1.00  ------ Proving...
% 3.48/1.00  ------ Problem Properties 
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  clauses                                 15
% 3.48/1.00  conjectures                             2
% 3.48/1.00  EPR                                     5
% 3.48/1.00  Horn                                    15
% 3.48/1.00  unary                                   6
% 3.48/1.00  binary                                  6
% 3.48/1.00  lits                                    29
% 3.48/1.00  lits eq                                 9
% 3.48/1.00  fd_pure                                 0
% 3.48/1.00  fd_pseudo                               0
% 3.48/1.00  fd_cond                                 1
% 3.48/1.00  fd_pseudo_cond                          0
% 3.48/1.00  AC symbols                              0
% 3.48/1.00  
% 3.48/1.00  ------ Input Options Time Limit: Unbounded
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ 
% 3.48/1.00  Current options:
% 3.48/1.00  ------ 
% 3.48/1.00  
% 3.48/1.00  ------ Input Options
% 3.48/1.00  
% 3.48/1.00  --out_options                           all
% 3.48/1.00  --tptp_safe_out                         true
% 3.48/1.00  --problem_path                          ""
% 3.48/1.00  --include_path                          ""
% 3.48/1.00  --clausifier                            res/vclausify_rel
% 3.48/1.00  --clausifier_options                    --mode clausify
% 3.48/1.00  --stdin                                 false
% 3.48/1.00  --stats_out                             sel
% 3.48/1.00  
% 3.48/1.00  ------ General Options
% 3.48/1.00  
% 3.48/1.00  --fof                                   false
% 3.48/1.00  --time_out_real                         604.99
% 3.48/1.00  --time_out_virtual                      -1.
% 3.48/1.00  --symbol_type_check                     false
% 3.48/1.00  --clausify_out                          false
% 3.48/1.00  --sig_cnt_out                           false
% 3.48/1.00  --trig_cnt_out                          false
% 3.48/1.00  --trig_cnt_out_tolerance                1.
% 3.48/1.00  --trig_cnt_out_sk_spl                   false
% 3.48/1.00  --abstr_cl_out                          false
% 3.48/1.00  
% 3.48/1.00  ------ Global Options
% 3.48/1.00  
% 3.48/1.00  --schedule                              none
% 3.48/1.00  --add_important_lit                     false
% 3.48/1.00  --prop_solver_per_cl                    1000
% 3.48/1.00  --min_unsat_core                        false
% 3.48/1.00  --soft_assumptions                      false
% 3.48/1.00  --soft_lemma_size                       3
% 3.48/1.00  --prop_impl_unit_size                   0
% 3.48/1.00  --prop_impl_unit                        []
% 3.48/1.00  --share_sel_clauses                     true
% 3.48/1.00  --reset_solvers                         false
% 3.48/1.00  --bc_imp_inh                            [conj_cone]
% 3.48/1.00  --conj_cone_tolerance                   3.
% 3.48/1.00  --extra_neg_conj                        none
% 3.48/1.00  --large_theory_mode                     true
% 3.48/1.00  --prolific_symb_bound                   200
% 3.48/1.00  --lt_threshold                          2000
% 3.48/1.00  --clause_weak_htbl                      true
% 3.48/1.00  --gc_record_bc_elim                     false
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing Options
% 3.48/1.00  
% 3.48/1.00  --preprocessing_flag                    true
% 3.48/1.00  --time_out_prep_mult                    0.1
% 3.48/1.00  --splitting_mode                        input
% 3.48/1.00  --splitting_grd                         true
% 3.48/1.00  --splitting_cvd                         false
% 3.48/1.00  --splitting_cvd_svl                     false
% 3.48/1.00  --splitting_nvd                         32
% 3.48/1.00  --sub_typing                            true
% 3.48/1.00  --prep_gs_sim                           false
% 3.48/1.00  --prep_unflatten                        true
% 3.48/1.00  --prep_res_sim                          true
% 3.48/1.00  --prep_upred                            true
% 3.48/1.00  --prep_sem_filter                       exhaustive
% 3.48/1.00  --prep_sem_filter_out                   false
% 3.48/1.00  --pred_elim                             false
% 3.48/1.00  --res_sim_input                         true
% 3.48/1.00  --eq_ax_congr_red                       true
% 3.48/1.00  --pure_diseq_elim                       true
% 3.48/1.00  --brand_transform                       false
% 3.48/1.00  --non_eq_to_eq                          false
% 3.48/1.00  --prep_def_merge                        true
% 3.48/1.00  --prep_def_merge_prop_impl              false
% 3.48/1.00  --prep_def_merge_mbd                    true
% 3.48/1.00  --prep_def_merge_tr_red                 false
% 3.48/1.00  --prep_def_merge_tr_cl                  false
% 3.48/1.00  --smt_preprocessing                     true
% 3.48/1.00  --smt_ac_axioms                         fast
% 3.48/1.00  --preprocessed_out                      false
% 3.48/1.00  --preprocessed_stats                    false
% 3.48/1.00  
% 3.48/1.00  ------ Abstraction refinement Options
% 3.48/1.00  
% 3.48/1.00  --abstr_ref                             []
% 3.48/1.00  --abstr_ref_prep                        false
% 3.48/1.00  --abstr_ref_until_sat                   false
% 3.48/1.00  --abstr_ref_sig_restrict                funpre
% 3.48/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/1.00  --abstr_ref_under                       []
% 3.48/1.00  
% 3.48/1.00  ------ SAT Options
% 3.48/1.00  
% 3.48/1.00  --sat_mode                              false
% 3.48/1.00  --sat_fm_restart_options                ""
% 3.48/1.00  --sat_gr_def                            false
% 3.48/1.00  --sat_epr_types                         true
% 3.48/1.00  --sat_non_cyclic_types                  false
% 3.48/1.00  --sat_finite_models                     false
% 3.48/1.00  --sat_fm_lemmas                         false
% 3.48/1.00  --sat_fm_prep                           false
% 3.48/1.00  --sat_fm_uc_incr                        true
% 3.48/1.00  --sat_out_model                         small
% 3.48/1.00  --sat_out_clauses                       false
% 3.48/1.00  
% 3.48/1.00  ------ QBF Options
% 3.48/1.00  
% 3.48/1.00  --qbf_mode                              false
% 3.48/1.00  --qbf_elim_univ                         false
% 3.48/1.00  --qbf_dom_inst                          none
% 3.48/1.00  --qbf_dom_pre_inst                      false
% 3.48/1.00  --qbf_sk_in                             false
% 3.48/1.00  --qbf_pred_elim                         true
% 3.48/1.00  --qbf_split                             512
% 3.48/1.00  
% 3.48/1.00  ------ BMC1 Options
% 3.48/1.00  
% 3.48/1.00  --bmc1_incremental                      false
% 3.48/1.00  --bmc1_axioms                           reachable_all
% 3.48/1.00  --bmc1_min_bound                        0
% 3.48/1.00  --bmc1_max_bound                        -1
% 3.48/1.00  --bmc1_max_bound_default                -1
% 3.48/1.00  --bmc1_symbol_reachability              true
% 3.48/1.00  --bmc1_property_lemmas                  false
% 3.48/1.00  --bmc1_k_induction                      false
% 3.48/1.00  --bmc1_non_equiv_states                 false
% 3.48/1.00  --bmc1_deadlock                         false
% 3.48/1.00  --bmc1_ucm                              false
% 3.48/1.00  --bmc1_add_unsat_core                   none
% 3.48/1.00  --bmc1_unsat_core_children              false
% 3.48/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/1.00  --bmc1_out_stat                         full
% 3.48/1.00  --bmc1_ground_init                      false
% 3.48/1.00  --bmc1_pre_inst_next_state              false
% 3.48/1.00  --bmc1_pre_inst_state                   false
% 3.48/1.00  --bmc1_pre_inst_reach_state             false
% 3.48/1.00  --bmc1_out_unsat_core                   false
% 3.48/1.00  --bmc1_aig_witness_out                  false
% 3.48/1.00  --bmc1_verbose                          false
% 3.48/1.00  --bmc1_dump_clauses_tptp                false
% 3.48/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.48/1.00  --bmc1_dump_file                        -
% 3.48/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.48/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.48/1.00  --bmc1_ucm_extend_mode                  1
% 3.48/1.00  --bmc1_ucm_init_mode                    2
% 3.48/1.00  --bmc1_ucm_cone_mode                    none
% 3.48/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.48/1.00  --bmc1_ucm_relax_model                  4
% 3.48/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.48/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/1.00  --bmc1_ucm_layered_model                none
% 3.48/1.00  --bmc1_ucm_max_lemma_size               10
% 3.48/1.00  
% 3.48/1.00  ------ AIG Options
% 3.48/1.00  
% 3.48/1.00  --aig_mode                              false
% 3.48/1.00  
% 3.48/1.00  ------ Instantiation Options
% 3.48/1.00  
% 3.48/1.00  --instantiation_flag                    true
% 3.48/1.00  --inst_sos_flag                         false
% 3.48/1.00  --inst_sos_phase                        true
% 3.48/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/1.00  --inst_lit_sel_side                     num_symb
% 3.48/1.00  --inst_solver_per_active                1400
% 3.48/1.00  --inst_solver_calls_frac                1.
% 3.48/1.00  --inst_passive_queue_type               priority_queues
% 3.48/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/1.00  --inst_passive_queues_freq              [25;2]
% 3.48/1.00  --inst_dismatching                      true
% 3.48/1.00  --inst_eager_unprocessed_to_passive     true
% 3.48/1.00  --inst_prop_sim_given                   true
% 3.48/1.00  --inst_prop_sim_new                     false
% 3.48/1.00  --inst_subs_new                         false
% 3.48/1.00  --inst_eq_res_simp                      false
% 3.48/1.00  --inst_subs_given                       false
% 3.48/1.00  --inst_orphan_elimination               true
% 3.48/1.00  --inst_learning_loop_flag               true
% 3.48/1.00  --inst_learning_start                   3000
% 3.48/1.00  --inst_learning_factor                  2
% 3.48/1.00  --inst_start_prop_sim_after_learn       3
% 3.48/1.00  --inst_sel_renew                        solver
% 3.48/1.00  --inst_lit_activity_flag                true
% 3.48/1.00  --inst_restr_to_given                   false
% 3.48/1.00  --inst_activity_threshold               500
% 3.48/1.00  --inst_out_proof                        true
% 3.48/1.00  
% 3.48/1.00  ------ Resolution Options
% 3.48/1.00  
% 3.48/1.00  --resolution_flag                       true
% 3.48/1.00  --res_lit_sel                           adaptive
% 3.48/1.00  --res_lit_sel_side                      none
% 3.48/1.00  --res_ordering                          kbo
% 3.48/1.00  --res_to_prop_solver                    active
% 3.48/1.00  --res_prop_simpl_new                    false
% 3.48/1.00  --res_prop_simpl_given                  true
% 3.48/1.00  --res_passive_queue_type                priority_queues
% 3.48/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/1.00  --res_passive_queues_freq               [15;5]
% 3.48/1.00  --res_forward_subs                      full
% 3.48/1.00  --res_backward_subs                     full
% 3.48/1.00  --res_forward_subs_resolution           true
% 3.48/1.00  --res_backward_subs_resolution          true
% 3.48/1.00  --res_orphan_elimination                true
% 3.48/1.00  --res_time_limit                        2.
% 3.48/1.00  --res_out_proof                         true
% 3.48/1.00  
% 3.48/1.00  ------ Superposition Options
% 3.48/1.00  
% 3.48/1.00  --superposition_flag                    true
% 3.48/1.00  --sup_passive_queue_type                priority_queues
% 3.48/1.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/1.00  --sup_passive_queues_freq               [1;4]
% 3.48/1.00  --demod_completeness_check              fast
% 3.48/1.00  --demod_use_ground                      true
% 3.48/1.00  --sup_to_prop_solver                    passive
% 3.48/1.00  --sup_prop_simpl_new                    true
% 3.48/1.00  --sup_prop_simpl_given                  true
% 3.48/1.00  --sup_fun_splitting                     false
% 3.48/1.00  --sup_smt_interval                      50000
% 3.48/1.00  
% 3.48/1.00  ------ Superposition Simplification Setup
% 3.48/1.00  
% 3.48/1.00  --sup_indices_passive                   []
% 3.48/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.00  --sup_full_bw                           [BwDemod]
% 3.48/1.00  --sup_immed_triv                        [TrivRules]
% 3.48/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.00  --sup_immed_bw_main                     []
% 3.48/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/1.00  
% 3.48/1.00  ------ Combination Options
% 3.48/1.00  
% 3.48/1.00  --comb_res_mult                         3
% 3.48/1.00  --comb_sup_mult                         2
% 3.48/1.00  --comb_inst_mult                        10
% 3.48/1.00  
% 3.48/1.00  ------ Debug Options
% 3.48/1.00  
% 3.48/1.00  --dbg_backtrace                         false
% 3.48/1.00  --dbg_dump_prop_clauses                 false
% 3.48/1.00  --dbg_dump_prop_clauses_file            -
% 3.48/1.00  --dbg_out_stat                          false
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  ------ Proving...
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  % SZS status Theorem for theBenchmark.p
% 3.48/1.00  
% 3.48/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/1.00  
% 3.48/1.00  fof(f18,conjecture,(
% 3.48/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f19,negated_conjecture,(
% 3.48/1.00    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.48/1.00    inference(negated_conjecture,[],[f18])).
% 3.48/1.00  
% 3.48/1.00  fof(f31,plain,(
% 3.48/1.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.48/1.00    inference(ennf_transformation,[],[f19])).
% 3.48/1.00  
% 3.48/1.00  fof(f32,plain,(
% 3.48/1.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 3.48/1.00    introduced(choice_axiom,[])).
% 3.48/1.00  
% 3.48/1.00  fof(f33,plain,(
% 3.48/1.00    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 3.48/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.48/1.00  
% 3.48/1.00  fof(f52,plain,(
% 3.48/1.00    v1_relat_1(sK0)),
% 3.48/1.00    inference(cnf_transformation,[],[f33])).
% 3.48/1.00  
% 3.48/1.00  fof(f1,axiom,(
% 3.48/1.00    v1_xboole_0(k1_xboole_0)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f34,plain,(
% 3.48/1.00    v1_xboole_0(k1_xboole_0)),
% 3.48/1.00    inference(cnf_transformation,[],[f1])).
% 3.48/1.00  
% 3.48/1.00  fof(f12,axiom,(
% 3.48/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f23,plain,(
% 3.48/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.48/1.00    inference(ennf_transformation,[],[f12])).
% 3.48/1.00  
% 3.48/1.00  fof(f45,plain,(
% 3.48/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f23])).
% 3.48/1.00  
% 3.48/1.00  fof(f13,axiom,(
% 3.48/1.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f24,plain,(
% 3.48/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.48/1.00    inference(ennf_transformation,[],[f13])).
% 3.48/1.00  
% 3.48/1.00  fof(f25,plain,(
% 3.48/1.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.48/1.00    inference(flattening,[],[f24])).
% 3.48/1.00  
% 3.48/1.00  fof(f46,plain,(
% 3.48/1.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f25])).
% 3.48/1.00  
% 3.48/1.00  fof(f14,axiom,(
% 3.48/1.00    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f26,plain,(
% 3.48/1.00    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.48/1.00    inference(ennf_transformation,[],[f14])).
% 3.48/1.00  
% 3.48/1.00  fof(f47,plain,(
% 3.48/1.00    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f26])).
% 3.48/1.00  
% 3.48/1.00  fof(f11,axiom,(
% 3.48/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f44,plain,(
% 3.48/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.48/1.00    inference(cnf_transformation,[],[f11])).
% 3.48/1.00  
% 3.48/1.00  fof(f5,axiom,(
% 3.48/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f38,plain,(
% 3.48/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f5])).
% 3.48/1.00  
% 3.48/1.00  fof(f6,axiom,(
% 3.48/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f39,plain,(
% 3.48/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f6])).
% 3.48/1.00  
% 3.48/1.00  fof(f7,axiom,(
% 3.48/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f40,plain,(
% 3.48/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f7])).
% 3.48/1.00  
% 3.48/1.00  fof(f8,axiom,(
% 3.48/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f41,plain,(
% 3.48/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f8])).
% 3.48/1.00  
% 3.48/1.00  fof(f54,plain,(
% 3.48/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.48/1.00    inference(definition_unfolding,[],[f40,f41])).
% 3.48/1.00  
% 3.48/1.00  fof(f55,plain,(
% 3.48/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.48/1.00    inference(definition_unfolding,[],[f39,f54])).
% 3.48/1.00  
% 3.48/1.00  fof(f56,plain,(
% 3.48/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.48/1.00    inference(definition_unfolding,[],[f38,f55])).
% 3.48/1.00  
% 3.48/1.00  fof(f57,plain,(
% 3.48/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.48/1.00    inference(definition_unfolding,[],[f44,f56])).
% 3.48/1.00  
% 3.48/1.00  fof(f59,plain,(
% 3.48/1.00    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 3.48/1.00    inference(definition_unfolding,[],[f47,f57])).
% 3.48/1.00  
% 3.48/1.00  fof(f17,axiom,(
% 3.48/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f51,plain,(
% 3.48/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.48/1.00    inference(cnf_transformation,[],[f17])).
% 3.48/1.00  
% 3.48/1.00  fof(f15,axiom,(
% 3.48/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f27,plain,(
% 3.48/1.00    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.48/1.00    inference(ennf_transformation,[],[f15])).
% 3.48/1.00  
% 3.48/1.00  fof(f28,plain,(
% 3.48/1.00    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.48/1.00    inference(flattening,[],[f27])).
% 3.48/1.00  
% 3.48/1.00  fof(f48,plain,(
% 3.48/1.00    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f28])).
% 3.48/1.00  
% 3.48/1.00  fof(f50,plain,(
% 3.48/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.48/1.00    inference(cnf_transformation,[],[f17])).
% 3.48/1.00  
% 3.48/1.00  fof(f4,axiom,(
% 3.48/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f37,plain,(
% 3.48/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f4])).
% 3.48/1.00  
% 3.48/1.00  fof(f3,axiom,(
% 3.48/1.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f36,plain,(
% 3.48/1.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f3])).
% 3.48/1.00  
% 3.48/1.00  fof(f58,plain,(
% 3.48/1.00    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 3.48/1.00    inference(definition_unfolding,[],[f36,f57])).
% 3.48/1.00  
% 3.48/1.00  fof(f10,axiom,(
% 3.48/1.00    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f22,plain,(
% 3.48/1.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.48/1.00    inference(ennf_transformation,[],[f10])).
% 3.48/1.00  
% 3.48/1.00  fof(f43,plain,(
% 3.48/1.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f22])).
% 3.48/1.00  
% 3.48/1.00  fof(f2,axiom,(
% 3.48/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f20,plain,(
% 3.48/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.48/1.00    inference(ennf_transformation,[],[f2])).
% 3.48/1.00  
% 3.48/1.00  fof(f35,plain,(
% 3.48/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f20])).
% 3.48/1.00  
% 3.48/1.00  fof(f16,axiom,(
% 3.48/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f29,plain,(
% 3.48/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.48/1.00    inference(ennf_transformation,[],[f16])).
% 3.48/1.00  
% 3.48/1.00  fof(f30,plain,(
% 3.48/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.48/1.00    inference(flattening,[],[f29])).
% 3.48/1.00  
% 3.48/1.00  fof(f49,plain,(
% 3.48/1.00    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f30])).
% 3.48/1.00  
% 3.48/1.00  fof(f9,axiom,(
% 3.48/1.00    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.48/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/1.00  
% 3.48/1.00  fof(f21,plain,(
% 3.48/1.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 3.48/1.00    inference(ennf_transformation,[],[f9])).
% 3.48/1.00  
% 3.48/1.00  fof(f42,plain,(
% 3.48/1.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 3.48/1.00    inference(cnf_transformation,[],[f21])).
% 3.48/1.00  
% 3.48/1.00  fof(f53,plain,(
% 3.48/1.00    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 3.48/1.00    inference(cnf_transformation,[],[f33])).
% 3.48/1.00  
% 3.48/1.00  cnf(c_14,negated_conjecture,
% 3.48/1.00      ( v1_relat_1(sK0) ),
% 3.48/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_115,negated_conjecture,
% 3.48/1.00      ( v1_relat_1(sK0) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_361,plain,
% 3.48/1.00      ( v1_relat_1(sK0) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_115]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_0,plain,
% 3.48/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.48/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_129,plain,
% 3.48/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_351,plain,
% 3.48/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_129]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_6,plain,
% 3.48/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.48/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_123,plain,
% 3.48/1.00      ( v1_relat_1(X0_39) | ~ v1_xboole_0(X0_39) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_356,plain,
% 3.48/1.00      ( v1_relat_1(X0_39) = iProver_top
% 3.48/1.00      | v1_xboole_0(X0_39) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_123]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_639,plain,
% 3.48/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_351,c_356]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_7,plain,
% 3.48/1.00      ( ~ v1_relat_1(X0)
% 3.48/1.00      | ~ v1_relat_1(X1)
% 3.48/1.00      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_122,plain,
% 3.48/1.00      ( ~ v1_relat_1(X0_39)
% 3.48/1.00      | ~ v1_relat_1(X1_39)
% 3.48/1.00      | v1_relat_1(k5_relat_1(X1_39,X0_39)) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_357,plain,
% 3.48/1.00      ( v1_relat_1(X0_39) != iProver_top
% 3.48/1.00      | v1_relat_1(X1_39) != iProver_top
% 3.48/1.00      | v1_relat_1(k5_relat_1(X1_39,X0_39)) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_122]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_8,plain,
% 3.48/1.00      ( ~ v1_relat_1(X0)
% 3.48/1.00      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 3.48/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_121,plain,
% 3.48/1.00      ( ~ v1_relat_1(X0_39)
% 3.48/1.00      | k1_setfam_1(k4_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,k2_zfmisc_1(k1_relat_1(X0_39),k2_relat_1(X0_39)))) = X0_39 ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_358,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,k2_zfmisc_1(k1_relat_1(X0_39),k2_relat_1(X0_39)))) = X0_39
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_121]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_867,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0_39,X1_39),k5_relat_1(X0_39,X1_39),k5_relat_1(X0_39,X1_39),k5_relat_1(X0_39,X1_39),k5_relat_1(X0_39,X1_39),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0_39,X1_39)),k2_relat_1(k5_relat_1(X0_39,X1_39))))) = k5_relat_1(X0_39,X1_39)
% 3.48/1.00      | v1_relat_1(X1_39) != iProver_top
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_357,c_358]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_2520,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,X0_39),k5_relat_1(k1_xboole_0,X0_39),k5_relat_1(k1_xboole_0,X0_39),k5_relat_1(k1_xboole_0,X0_39),k5_relat_1(k1_xboole_0,X0_39),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)),k2_relat_1(k5_relat_1(k1_xboole_0,X0_39))))) = k5_relat_1(k1_xboole_0,X0_39)
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_639,c_867]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12789,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_361,c_2520]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_11,plain,
% 3.48/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.48/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_118,plain,
% 3.48/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_9,plain,
% 3.48/1.00      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.48/1.00      | ~ v1_relat_1(X1)
% 3.48/1.00      | ~ v1_relat_1(X0)
% 3.48/1.00      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.48/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_120,plain,
% 3.48/1.00      ( ~ r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39))
% 3.48/1.00      | ~ v1_relat_1(X1_39)
% 3.48/1.00      | ~ v1_relat_1(X0_39)
% 3.48/1.00      | k1_relat_1(k5_relat_1(X0_39,X1_39)) = k1_relat_1(X0_39) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_359,plain,
% 3.48/1.00      ( k1_relat_1(k5_relat_1(X0_39,X1_39)) = k1_relat_1(X0_39)
% 3.48/1.00      | r1_tarski(k2_relat_1(X0_39),k1_relat_1(X1_39)) != iProver_top
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top
% 3.48/1.00      | v1_relat_1(X1_39) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_120]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_884,plain,
% 3.48/1.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_relat_1(k1_xboole_0)
% 3.48/1.00      | r1_tarski(k1_xboole_0,k1_relat_1(X0_39)) != iProver_top
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top
% 3.48/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_118,c_359]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12,plain,
% 3.48/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.48/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_117,plain,
% 3.48/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_898,plain,
% 3.48/1.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_xboole_0
% 3.48/1.00      | r1_tarski(k1_xboole_0,k1_relat_1(X0_39)) != iProver_top
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top
% 3.48/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(light_normalisation,[status(thm)],[c_884,c_117]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_28,plain,
% 3.48/1.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_30,plain,
% 3.48/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.48/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_42,plain,
% 3.48/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_974,plain,
% 3.48/1.00      ( v1_relat_1(X0_39) != iProver_top
% 3.48/1.00      | r1_tarski(k1_xboole_0,k1_relat_1(X0_39)) != iProver_top
% 3.48/1.00      | k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_xboole_0 ),
% 3.48/1.00      inference(global_propositional_subsumption,
% 3.48/1.00                [status(thm)],
% 3.48/1.00                [c_898,c_30,c_42]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_975,plain,
% 3.48/1.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_xboole_0
% 3.48/1.00      | r1_tarski(k1_xboole_0,k1_relat_1(X0_39)) != iProver_top
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.48/1.00      inference(renaming,[status(thm)],[c_974]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_3,plain,
% 3.48/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.48/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_126,plain,
% 3.48/1.00      ( r1_tarski(k1_xboole_0,X0_39) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_353,plain,
% 3.48/1.00      ( r1_tarski(k1_xboole_0,X0_39) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_126]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_981,plain,
% 3.48/1.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_39)) = k1_xboole_0
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.48/1.00      inference(forward_subsumption_resolution,
% 3.48/1.00                [status(thm)],
% 3.48/1.00                [c_975,c_353]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_985,plain,
% 3.48/1.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_361,c_981]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12813,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.48/1.00      inference(light_normalisation,[status(thm)],[c_12789,c_985]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_2,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.48/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_127,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(X0_39,X0_39,X0_39,X0_39,X0_39,k1_xboole_0)) = k1_xboole_0 ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_5,plain,
% 3.48/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_124,plain,
% 3.48/1.00      ( ~ v1_xboole_0(X0_39) | v1_xboole_0(k2_zfmisc_1(X0_39,X1_39)) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_355,plain,
% 3.48/1.00      ( v1_xboole_0(X0_39) != iProver_top
% 3.48/1.00      | v1_xboole_0(k2_zfmisc_1(X0_39,X1_39)) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_124]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_1,plain,
% 3.48/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.48/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_128,plain,
% 3.48/1.00      ( ~ v1_xboole_0(X0_39) | k1_xboole_0 = X0_39 ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_352,plain,
% 3.48/1.00      ( k1_xboole_0 = X0_39 | v1_xboole_0(X0_39) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_128]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_770,plain,
% 3.48/1.00      ( k2_zfmisc_1(X0_39,X1_39) = k1_xboole_0
% 3.48/1.00      | v1_xboole_0(X0_39) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_355,c_352]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_1970,plain,
% 3.48/1.00      ( k2_zfmisc_1(k1_xboole_0,X0_39) = k1_xboole_0 ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_351,c_770]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12814,plain,
% 3.48/1.00      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 3.48/1.00      inference(demodulation,[status(thm)],[c_12813,c_127,c_1970]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_2519,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,X0_39),k5_relat_1(sK0,X0_39),k5_relat_1(sK0,X0_39),k5_relat_1(sK0,X0_39),k5_relat_1(sK0,X0_39),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0_39)),k2_relat_1(k5_relat_1(sK0,X0_39))))) = k5_relat_1(sK0,X0_39)
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_361,c_867]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12192,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_639,c_2519]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_10,plain,
% 3.48/1.00      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 3.48/1.00      | ~ v1_relat_1(X1)
% 3.48/1.00      | ~ v1_relat_1(X0)
% 3.48/1.00      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 3.48/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_119,plain,
% 3.48/1.00      ( ~ r1_tarski(k1_relat_1(X0_39),k2_relat_1(X1_39))
% 3.48/1.00      | ~ v1_relat_1(X1_39)
% 3.48/1.00      | ~ v1_relat_1(X0_39)
% 3.48/1.00      | k2_relat_1(k5_relat_1(X1_39,X0_39)) = k2_relat_1(X0_39) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_360,plain,
% 3.48/1.00      ( k2_relat_1(k5_relat_1(X0_39,X1_39)) = k2_relat_1(X1_39)
% 3.48/1.00      | r1_tarski(k1_relat_1(X1_39),k2_relat_1(X0_39)) != iProver_top
% 3.48/1.00      | v1_relat_1(X1_39) != iProver_top
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_119]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_1003,plain,
% 3.48/1.00      ( k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 3.48/1.00      | r1_tarski(k1_xboole_0,k2_relat_1(X0_39)) != iProver_top
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top
% 3.48/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_117,c_360]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_1017,plain,
% 3.48/1.00      ( k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k1_xboole_0
% 3.48/1.00      | r1_tarski(k1_xboole_0,k2_relat_1(X0_39)) != iProver_top
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top
% 3.48/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.48/1.00      inference(light_normalisation,[status(thm)],[c_1003,c_118]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_1112,plain,
% 3.48/1.00      ( v1_relat_1(X0_39) != iProver_top
% 3.48/1.00      | r1_tarski(k1_xboole_0,k2_relat_1(X0_39)) != iProver_top
% 3.48/1.00      | k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k1_xboole_0 ),
% 3.48/1.00      inference(global_propositional_subsumption,
% 3.48/1.00                [status(thm)],
% 3.48/1.00                [c_1017,c_30,c_42]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_1113,plain,
% 3.48/1.00      ( k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k1_xboole_0
% 3.48/1.00      | r1_tarski(k1_xboole_0,k2_relat_1(X0_39)) != iProver_top
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.48/1.00      inference(renaming,[status(thm)],[c_1112]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_1119,plain,
% 3.48/1.00      ( k2_relat_1(k5_relat_1(X0_39,k1_xboole_0)) = k1_xboole_0
% 3.48/1.00      | v1_relat_1(X0_39) != iProver_top ),
% 3.48/1.00      inference(forward_subsumption_resolution,
% 3.48/1.00                [status(thm)],
% 3.48/1.00                [c_1113,c_353]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_1123,plain,
% 3.48/1.00      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_361,c_1119]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12211,plain,
% 3.48/1.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.48/1.00      inference(light_normalisation,[status(thm)],[c_12192,c_1123]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_4,plain,
% 3.48/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 3.48/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_125,plain,
% 3.48/1.00      ( ~ v1_xboole_0(X0_39) | v1_xboole_0(k2_zfmisc_1(X1_39,X0_39)) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_354,plain,
% 3.48/1.00      ( v1_xboole_0(X0_39) != iProver_top
% 3.48/1.00      | v1_xboole_0(k2_zfmisc_1(X1_39,X0_39)) = iProver_top ),
% 3.48/1.00      inference(predicate_to_equality,[status(thm)],[c_125]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_645,plain,
% 3.48/1.00      ( k2_zfmisc_1(X0_39,X1_39) = k1_xboole_0
% 3.48/1.00      | v1_xboole_0(X1_39) != iProver_top ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_354,c_352]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_1614,plain,
% 3.48/1.00      ( k2_zfmisc_1(X0_39,k1_xboole_0) = k1_xboole_0 ),
% 3.48/1.00      inference(superposition,[status(thm)],[c_351,c_645]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12212,plain,
% 3.48/1.00      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.48/1.00      inference(demodulation,[status(thm)],[c_12211,c_127,c_1614]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_13,negated_conjecture,
% 3.48/1.00      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 3.48/1.00      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 3.48/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_116,negated_conjecture,
% 3.48/1.00      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 3.48/1.00      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 3.48/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12475,plain,
% 3.48/1.00      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 3.48/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.48/1.00      inference(demodulation,[status(thm)],[c_12212,c_116]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_12476,plain,
% 3.48/1.00      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
% 3.48/1.00      inference(equality_resolution_simp,[status(thm)],[c_12475]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(contradiction,plain,
% 3.48/1.00      ( $false ),
% 3.48/1.00      inference(minisat,[status(thm)],[c_12814,c_12476]) ).
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/1.00  
% 3.48/1.00  ------                               Statistics
% 3.48/1.00  
% 3.48/1.00  ------ Selected
% 3.48/1.00  
% 3.48/1.00  total_time:                             0.477
% 3.48/1.00  
%------------------------------------------------------------------------------
