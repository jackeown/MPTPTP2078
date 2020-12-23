%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:56 EST 2020

% Result     : Theorem 35.59s
% Output     : CNFRefutation 35.59s
% Verified   : 
% Statistics : Number of formulae       :  163 (1130 expanded)
%              Number of clauses        :   95 ( 446 expanded)
%              Number of leaves         :   22 ( 245 expanded)
%              Depth                    :   27
%              Number of atoms          :  320 (1990 expanded)
%              Number of equality atoms :  211 (1092 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f36,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

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

fof(f66,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f70])).

fof(f73,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f71])).

fof(f21,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_566,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_582,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_575,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1011,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_582,c_575])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_573,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_571,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1766,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_571])).

cnf(c_8210,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1766])).

cnf(c_105566,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_566,c_8210])).

cnf(c_19,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_16,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_568,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1004,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_568])).

cnf(c_47,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_49,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_66,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1787,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1004,c_49,c_66])).

cnf(c_1788,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1787])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_578,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_580,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1565,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_580])).

cnf(c_2641,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1788,c_1565])).

cnf(c_13444,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_566,c_2641])).

cnf(c_105598,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_105566,c_13444])).

cnf(c_5,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_576,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_581,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1425,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_576,c_581])).

cnf(c_2844,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_582,c_1425])).

cnf(c_105599,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_105598,c_5,c_2844])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_574,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_567,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1174,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k4_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_567])).

cnf(c_2803,plain,
    ( k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_566,c_1174])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_572,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1169,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_566,c_572])).

cnf(c_2812,plain,
    ( k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2803,c_1169])).

cnf(c_17245,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(X0),k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_2812])).

cnf(c_17874,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(X0)),k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0))))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_17245])).

cnf(c_36859,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_1011,c_17874])).

cnf(c_1765,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k2_zfmisc_1(k1_relat_1(k4_relat_1(X0)),k2_relat_1(k4_relat_1(X0))))) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_571])).

cnf(c_7607,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0))))) = k4_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1011,c_1765])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_569,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1917,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1011,c_569])).

cnf(c_18,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1927,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1917,c_18])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_570,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1916,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1011,c_570])).

cnf(c_1930,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1916,c_19])).

cnf(c_7625,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = k4_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7607,c_1927,c_1930])).

cnf(c_7626,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7625,c_5,c_2844])).

cnf(c_1919,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_567])).

cnf(c_6299,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_566,c_1919])).

cnf(c_7653,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_7626,c_6299])).

cnf(c_7883,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7653,c_573])).

cnf(c_22,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_44,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_46,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_6677,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6299,c_573])).

cnf(c_19422,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_19423,plain,
    ( v1_relat_1(k4_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19422])).

cnf(c_28020,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7883,c_22,c_46,c_49,c_66,c_6677,c_19423])).

cnf(c_28075,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_28020,c_571])).

cnf(c_1566,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_568,c_580])).

cnf(c_7882,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7653,c_1566])).

cnf(c_7904,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7882,c_19,c_7653])).

cnf(c_6676,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0))) = k1_relat_1(k4_relat_1(k1_xboole_0))
    | r1_tarski(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6299,c_1566])).

cnf(c_6696,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6676,c_1927,c_6299])).

cnf(c_7913,plain,
    ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7904,c_46,c_49,c_66,c_6696])).

cnf(c_7914,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7913])).

cnf(c_7920,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7914,c_578])).

cnf(c_7922,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_7920])).

cnf(c_8177,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7922,c_22])).

cnf(c_28085,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_28075,c_8177])).

cnf(c_28086,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28085,c_5,c_2844])).

cnf(c_28559,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28086,c_7653])).

cnf(c_36878,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_36859,c_7626,c_28559])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_36906,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36878,c_20])).

cnf(c_36907,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_36906])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_105599,c_36907])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:51:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.59/4.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.59/4.99  
% 35.59/4.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.59/4.99  
% 35.59/4.99  ------  iProver source info
% 35.59/4.99  
% 35.59/4.99  git: date: 2020-06-30 10:37:57 +0100
% 35.59/4.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.59/4.99  git: non_committed_changes: false
% 35.59/4.99  git: last_make_outside_of_git: false
% 35.59/4.99  
% 35.59/4.99  ------ 
% 35.59/4.99  
% 35.59/4.99  ------ Input Options
% 35.59/4.99  
% 35.59/4.99  --out_options                           all
% 35.59/4.99  --tptp_safe_out                         true
% 35.59/4.99  --problem_path                          ""
% 35.59/4.99  --include_path                          ""
% 35.59/4.99  --clausifier                            res/vclausify_rel
% 35.59/4.99  --clausifier_options                    --mode clausify
% 35.59/4.99  --stdin                                 false
% 35.59/4.99  --stats_out                             sel
% 35.59/4.99  
% 35.59/4.99  ------ General Options
% 35.59/4.99  
% 35.59/4.99  --fof                                   false
% 35.59/4.99  --time_out_real                         604.99
% 35.59/4.99  --time_out_virtual                      -1.
% 35.59/4.99  --symbol_type_check                     false
% 35.59/4.99  --clausify_out                          false
% 35.59/4.99  --sig_cnt_out                           false
% 35.59/4.99  --trig_cnt_out                          false
% 35.59/4.99  --trig_cnt_out_tolerance                1.
% 35.59/4.99  --trig_cnt_out_sk_spl                   false
% 35.59/4.99  --abstr_cl_out                          false
% 35.59/4.99  
% 35.59/4.99  ------ Global Options
% 35.59/4.99  
% 35.59/4.99  --schedule                              none
% 35.59/4.99  --add_important_lit                     false
% 35.59/4.99  --prop_solver_per_cl                    1000
% 35.59/4.99  --min_unsat_core                        false
% 35.59/4.99  --soft_assumptions                      false
% 35.59/4.99  --soft_lemma_size                       3
% 35.59/4.99  --prop_impl_unit_size                   0
% 35.59/4.99  --prop_impl_unit                        []
% 35.59/4.99  --share_sel_clauses                     true
% 35.59/4.99  --reset_solvers                         false
% 35.59/4.99  --bc_imp_inh                            [conj_cone]
% 35.59/4.99  --conj_cone_tolerance                   3.
% 35.59/4.99  --extra_neg_conj                        none
% 35.59/4.99  --large_theory_mode                     true
% 35.59/4.99  --prolific_symb_bound                   200
% 35.59/4.99  --lt_threshold                          2000
% 35.59/4.99  --clause_weak_htbl                      true
% 35.59/4.99  --gc_record_bc_elim                     false
% 35.59/5.00  
% 35.59/5.00  ------ Preprocessing Options
% 35.59/5.00  
% 35.59/5.00  --preprocessing_flag                    true
% 35.59/5.00  --time_out_prep_mult                    0.1
% 35.59/5.00  --splitting_mode                        input
% 35.59/5.00  --splitting_grd                         true
% 35.59/5.00  --splitting_cvd                         false
% 35.59/5.00  --splitting_cvd_svl                     false
% 35.59/5.00  --splitting_nvd                         32
% 35.59/5.00  --sub_typing                            true
% 35.59/5.00  --prep_gs_sim                           false
% 35.59/5.00  --prep_unflatten                        true
% 35.59/5.00  --prep_res_sim                          true
% 35.59/5.00  --prep_upred                            true
% 35.59/5.00  --prep_sem_filter                       exhaustive
% 35.59/5.00  --prep_sem_filter_out                   false
% 35.59/5.00  --pred_elim                             false
% 35.59/5.00  --res_sim_input                         true
% 35.59/5.00  --eq_ax_congr_red                       true
% 35.59/5.00  --pure_diseq_elim                       true
% 35.59/5.00  --brand_transform                       false
% 35.59/5.00  --non_eq_to_eq                          false
% 35.59/5.00  --prep_def_merge                        true
% 35.59/5.00  --prep_def_merge_prop_impl              false
% 35.59/5.00  --prep_def_merge_mbd                    true
% 35.59/5.00  --prep_def_merge_tr_red                 false
% 35.59/5.00  --prep_def_merge_tr_cl                  false
% 35.59/5.00  --smt_preprocessing                     true
% 35.59/5.00  --smt_ac_axioms                         fast
% 35.59/5.00  --preprocessed_out                      false
% 35.59/5.00  --preprocessed_stats                    false
% 35.59/5.00  
% 35.59/5.00  ------ Abstraction refinement Options
% 35.59/5.00  
% 35.59/5.00  --abstr_ref                             []
% 35.59/5.00  --abstr_ref_prep                        false
% 35.59/5.00  --abstr_ref_until_sat                   false
% 35.59/5.00  --abstr_ref_sig_restrict                funpre
% 35.59/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.59/5.00  --abstr_ref_under                       []
% 35.59/5.00  
% 35.59/5.00  ------ SAT Options
% 35.59/5.00  
% 35.59/5.00  --sat_mode                              false
% 35.59/5.00  --sat_fm_restart_options                ""
% 35.59/5.00  --sat_gr_def                            false
% 35.59/5.00  --sat_epr_types                         true
% 35.59/5.00  --sat_non_cyclic_types                  false
% 35.59/5.00  --sat_finite_models                     false
% 35.59/5.00  --sat_fm_lemmas                         false
% 35.59/5.00  --sat_fm_prep                           false
% 35.59/5.00  --sat_fm_uc_incr                        true
% 35.59/5.00  --sat_out_model                         small
% 35.59/5.00  --sat_out_clauses                       false
% 35.59/5.00  
% 35.59/5.00  ------ QBF Options
% 35.59/5.00  
% 35.59/5.00  --qbf_mode                              false
% 35.59/5.00  --qbf_elim_univ                         false
% 35.59/5.00  --qbf_dom_inst                          none
% 35.59/5.00  --qbf_dom_pre_inst                      false
% 35.59/5.00  --qbf_sk_in                             false
% 35.59/5.00  --qbf_pred_elim                         true
% 35.59/5.00  --qbf_split                             512
% 35.59/5.00  
% 35.59/5.00  ------ BMC1 Options
% 35.59/5.00  
% 35.59/5.00  --bmc1_incremental                      false
% 35.59/5.00  --bmc1_axioms                           reachable_all
% 35.59/5.00  --bmc1_min_bound                        0
% 35.59/5.00  --bmc1_max_bound                        -1
% 35.59/5.00  --bmc1_max_bound_default                -1
% 35.59/5.00  --bmc1_symbol_reachability              true
% 35.59/5.00  --bmc1_property_lemmas                  false
% 35.59/5.00  --bmc1_k_induction                      false
% 35.59/5.00  --bmc1_non_equiv_states                 false
% 35.59/5.00  --bmc1_deadlock                         false
% 35.59/5.00  --bmc1_ucm                              false
% 35.59/5.00  --bmc1_add_unsat_core                   none
% 35.59/5.00  --bmc1_unsat_core_children              false
% 35.59/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.59/5.00  --bmc1_out_stat                         full
% 35.59/5.00  --bmc1_ground_init                      false
% 35.59/5.00  --bmc1_pre_inst_next_state              false
% 35.59/5.00  --bmc1_pre_inst_state                   false
% 35.59/5.00  --bmc1_pre_inst_reach_state             false
% 35.59/5.00  --bmc1_out_unsat_core                   false
% 35.59/5.00  --bmc1_aig_witness_out                  false
% 35.59/5.00  --bmc1_verbose                          false
% 35.59/5.00  --bmc1_dump_clauses_tptp                false
% 35.59/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.59/5.00  --bmc1_dump_file                        -
% 35.59/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.59/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.59/5.00  --bmc1_ucm_extend_mode                  1
% 35.59/5.00  --bmc1_ucm_init_mode                    2
% 35.59/5.00  --bmc1_ucm_cone_mode                    none
% 35.59/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.59/5.00  --bmc1_ucm_relax_model                  4
% 35.59/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.59/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.59/5.00  --bmc1_ucm_layered_model                none
% 35.59/5.00  --bmc1_ucm_max_lemma_size               10
% 35.59/5.00  
% 35.59/5.00  ------ AIG Options
% 35.59/5.00  
% 35.59/5.00  --aig_mode                              false
% 35.59/5.00  
% 35.59/5.00  ------ Instantiation Options
% 35.59/5.00  
% 35.59/5.00  --instantiation_flag                    true
% 35.59/5.00  --inst_sos_flag                         false
% 35.59/5.00  --inst_sos_phase                        true
% 35.59/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.59/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.59/5.00  --inst_lit_sel_side                     num_symb
% 35.59/5.00  --inst_solver_per_active                1400
% 35.59/5.00  --inst_solver_calls_frac                1.
% 35.59/5.00  --inst_passive_queue_type               priority_queues
% 35.59/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.59/5.00  --inst_passive_queues_freq              [25;2]
% 35.59/5.00  --inst_dismatching                      true
% 35.59/5.00  --inst_eager_unprocessed_to_passive     true
% 35.59/5.00  --inst_prop_sim_given                   true
% 35.59/5.00  --inst_prop_sim_new                     false
% 35.59/5.00  --inst_subs_new                         false
% 35.59/5.00  --inst_eq_res_simp                      false
% 35.59/5.00  --inst_subs_given                       false
% 35.59/5.00  --inst_orphan_elimination               true
% 35.59/5.00  --inst_learning_loop_flag               true
% 35.59/5.00  --inst_learning_start                   3000
% 35.59/5.00  --inst_learning_factor                  2
% 35.59/5.00  --inst_start_prop_sim_after_learn       3
% 35.59/5.00  --inst_sel_renew                        solver
% 35.59/5.00  --inst_lit_activity_flag                true
% 35.59/5.00  --inst_restr_to_given                   false
% 35.59/5.00  --inst_activity_threshold               500
% 35.59/5.00  --inst_out_proof                        true
% 35.59/5.00  
% 35.59/5.00  ------ Resolution Options
% 35.59/5.00  
% 35.59/5.00  --resolution_flag                       true
% 35.59/5.00  --res_lit_sel                           adaptive
% 35.59/5.00  --res_lit_sel_side                      none
% 35.59/5.00  --res_ordering                          kbo
% 35.59/5.00  --res_to_prop_solver                    active
% 35.59/5.00  --res_prop_simpl_new                    false
% 35.59/5.00  --res_prop_simpl_given                  true
% 35.59/5.00  --res_passive_queue_type                priority_queues
% 35.59/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.59/5.00  --res_passive_queues_freq               [15;5]
% 35.59/5.00  --res_forward_subs                      full
% 35.59/5.00  --res_backward_subs                     full
% 35.59/5.00  --res_forward_subs_resolution           true
% 35.59/5.00  --res_backward_subs_resolution          true
% 35.59/5.00  --res_orphan_elimination                true
% 35.59/5.00  --res_time_limit                        2.
% 35.59/5.00  --res_out_proof                         true
% 35.59/5.00  
% 35.59/5.00  ------ Superposition Options
% 35.59/5.00  
% 35.59/5.00  --superposition_flag                    true
% 35.59/5.00  --sup_passive_queue_type                priority_queues
% 35.59/5.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.59/5.00  --sup_passive_queues_freq               [1;4]
% 35.59/5.00  --demod_completeness_check              fast
% 35.59/5.00  --demod_use_ground                      true
% 35.59/5.00  --sup_to_prop_solver                    passive
% 35.59/5.00  --sup_prop_simpl_new                    true
% 35.59/5.00  --sup_prop_simpl_given                  true
% 35.59/5.00  --sup_fun_splitting                     false
% 35.59/5.00  --sup_smt_interval                      50000
% 35.59/5.00  
% 35.59/5.00  ------ Superposition Simplification Setup
% 35.59/5.00  
% 35.59/5.00  --sup_indices_passive                   []
% 35.59/5.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.59/5.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.59/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.59/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.59/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.59/5.00  --sup_full_bw                           [BwDemod]
% 35.59/5.00  --sup_immed_triv                        [TrivRules]
% 35.59/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.59/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.59/5.00  --sup_immed_bw_main                     []
% 35.59/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.59/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.59/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.59/5.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.59/5.00  
% 35.59/5.00  ------ Combination Options
% 35.59/5.00  
% 35.59/5.00  --comb_res_mult                         3
% 35.59/5.00  --comb_sup_mult                         2
% 35.59/5.00  --comb_inst_mult                        10
% 35.59/5.00  
% 35.59/5.00  ------ Debug Options
% 35.59/5.00  
% 35.59/5.00  --dbg_backtrace                         false
% 35.59/5.00  --dbg_dump_prop_clauses                 false
% 35.59/5.00  --dbg_dump_prop_clauses_file            -
% 35.59/5.00  --dbg_out_stat                          false
% 35.59/5.00  ------ Parsing...
% 35.59/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.59/5.00  
% 35.59/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 35.59/5.00  
% 35.59/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.59/5.00  
% 35.59/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.59/5.00  ------ Proving...
% 35.59/5.00  ------ Problem Properties 
% 35.59/5.00  
% 35.59/5.00  
% 35.59/5.00  clauses                                 21
% 35.59/5.00  conjectures                             2
% 35.59/5.00  EPR                                     7
% 35.59/5.00  Horn                                    21
% 35.59/5.00  unary                                   7
% 35.59/5.00  binary                                  10
% 35.59/5.00  lits                                    39
% 35.59/5.00  lits eq                                 12
% 35.59/5.00  fd_pure                                 0
% 35.59/5.00  fd_pseudo                               0
% 35.59/5.00  fd_cond                                 1
% 35.59/5.00  fd_pseudo_cond                          1
% 35.59/5.00  AC symbols                              0
% 35.59/5.00  
% 35.59/5.00  ------ Input Options Time Limit: Unbounded
% 35.59/5.00  
% 35.59/5.00  
% 35.59/5.00  ------ 
% 35.59/5.00  Current options:
% 35.59/5.00  ------ 
% 35.59/5.00  
% 35.59/5.00  ------ Input Options
% 35.59/5.00  
% 35.59/5.00  --out_options                           all
% 35.59/5.00  --tptp_safe_out                         true
% 35.59/5.00  --problem_path                          ""
% 35.59/5.00  --include_path                          ""
% 35.59/5.00  --clausifier                            res/vclausify_rel
% 35.59/5.00  --clausifier_options                    --mode clausify
% 35.59/5.00  --stdin                                 false
% 35.59/5.00  --stats_out                             sel
% 35.59/5.00  
% 35.59/5.00  ------ General Options
% 35.59/5.00  
% 35.59/5.00  --fof                                   false
% 35.59/5.00  --time_out_real                         604.99
% 35.59/5.00  --time_out_virtual                      -1.
% 35.59/5.00  --symbol_type_check                     false
% 35.59/5.00  --clausify_out                          false
% 35.59/5.00  --sig_cnt_out                           false
% 35.59/5.00  --trig_cnt_out                          false
% 35.59/5.00  --trig_cnt_out_tolerance                1.
% 35.59/5.00  --trig_cnt_out_sk_spl                   false
% 35.59/5.00  --abstr_cl_out                          false
% 35.59/5.00  
% 35.59/5.00  ------ Global Options
% 35.59/5.00  
% 35.59/5.00  --schedule                              none
% 35.59/5.00  --add_important_lit                     false
% 35.59/5.00  --prop_solver_per_cl                    1000
% 35.59/5.00  --min_unsat_core                        false
% 35.59/5.00  --soft_assumptions                      false
% 35.59/5.00  --soft_lemma_size                       3
% 35.59/5.00  --prop_impl_unit_size                   0
% 35.59/5.00  --prop_impl_unit                        []
% 35.59/5.00  --share_sel_clauses                     true
% 35.59/5.00  --reset_solvers                         false
% 35.59/5.00  --bc_imp_inh                            [conj_cone]
% 35.59/5.00  --conj_cone_tolerance                   3.
% 35.59/5.00  --extra_neg_conj                        none
% 35.59/5.00  --large_theory_mode                     true
% 35.59/5.00  --prolific_symb_bound                   200
% 35.59/5.00  --lt_threshold                          2000
% 35.59/5.00  --clause_weak_htbl                      true
% 35.59/5.00  --gc_record_bc_elim                     false
% 35.59/5.00  
% 35.59/5.00  ------ Preprocessing Options
% 35.59/5.00  
% 35.59/5.00  --preprocessing_flag                    true
% 35.59/5.00  --time_out_prep_mult                    0.1
% 35.59/5.00  --splitting_mode                        input
% 35.59/5.00  --splitting_grd                         true
% 35.59/5.00  --splitting_cvd                         false
% 35.59/5.00  --splitting_cvd_svl                     false
% 35.59/5.00  --splitting_nvd                         32
% 35.59/5.00  --sub_typing                            true
% 35.59/5.00  --prep_gs_sim                           false
% 35.59/5.00  --prep_unflatten                        true
% 35.59/5.00  --prep_res_sim                          true
% 35.59/5.00  --prep_upred                            true
% 35.59/5.00  --prep_sem_filter                       exhaustive
% 35.59/5.00  --prep_sem_filter_out                   false
% 35.59/5.00  --pred_elim                             false
% 35.59/5.00  --res_sim_input                         true
% 35.59/5.00  --eq_ax_congr_red                       true
% 35.59/5.00  --pure_diseq_elim                       true
% 35.59/5.00  --brand_transform                       false
% 35.59/5.00  --non_eq_to_eq                          false
% 35.59/5.00  --prep_def_merge                        true
% 35.59/5.00  --prep_def_merge_prop_impl              false
% 35.59/5.00  --prep_def_merge_mbd                    true
% 35.59/5.00  --prep_def_merge_tr_red                 false
% 35.59/5.00  --prep_def_merge_tr_cl                  false
% 35.59/5.00  --smt_preprocessing                     true
% 35.59/5.00  --smt_ac_axioms                         fast
% 35.59/5.00  --preprocessed_out                      false
% 35.59/5.00  --preprocessed_stats                    false
% 35.59/5.00  
% 35.59/5.00  ------ Abstraction refinement Options
% 35.59/5.00  
% 35.59/5.00  --abstr_ref                             []
% 35.59/5.00  --abstr_ref_prep                        false
% 35.59/5.00  --abstr_ref_until_sat                   false
% 35.59/5.00  --abstr_ref_sig_restrict                funpre
% 35.59/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.59/5.00  --abstr_ref_under                       []
% 35.59/5.00  
% 35.59/5.00  ------ SAT Options
% 35.59/5.00  
% 35.59/5.00  --sat_mode                              false
% 35.59/5.00  --sat_fm_restart_options                ""
% 35.59/5.00  --sat_gr_def                            false
% 35.59/5.00  --sat_epr_types                         true
% 35.59/5.00  --sat_non_cyclic_types                  false
% 35.59/5.00  --sat_finite_models                     false
% 35.59/5.00  --sat_fm_lemmas                         false
% 35.59/5.00  --sat_fm_prep                           false
% 35.59/5.00  --sat_fm_uc_incr                        true
% 35.59/5.00  --sat_out_model                         small
% 35.59/5.00  --sat_out_clauses                       false
% 35.59/5.00  
% 35.59/5.00  ------ QBF Options
% 35.59/5.00  
% 35.59/5.00  --qbf_mode                              false
% 35.59/5.00  --qbf_elim_univ                         false
% 35.59/5.00  --qbf_dom_inst                          none
% 35.59/5.00  --qbf_dom_pre_inst                      false
% 35.59/5.00  --qbf_sk_in                             false
% 35.59/5.00  --qbf_pred_elim                         true
% 35.59/5.00  --qbf_split                             512
% 35.59/5.00  
% 35.59/5.00  ------ BMC1 Options
% 35.59/5.00  
% 35.59/5.00  --bmc1_incremental                      false
% 35.59/5.00  --bmc1_axioms                           reachable_all
% 35.59/5.00  --bmc1_min_bound                        0
% 35.59/5.00  --bmc1_max_bound                        -1
% 35.59/5.00  --bmc1_max_bound_default                -1
% 35.59/5.00  --bmc1_symbol_reachability              true
% 35.59/5.00  --bmc1_property_lemmas                  false
% 35.59/5.00  --bmc1_k_induction                      false
% 35.59/5.00  --bmc1_non_equiv_states                 false
% 35.59/5.00  --bmc1_deadlock                         false
% 35.59/5.00  --bmc1_ucm                              false
% 35.59/5.00  --bmc1_add_unsat_core                   none
% 35.59/5.00  --bmc1_unsat_core_children              false
% 35.59/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.59/5.00  --bmc1_out_stat                         full
% 35.59/5.00  --bmc1_ground_init                      false
% 35.59/5.00  --bmc1_pre_inst_next_state              false
% 35.59/5.00  --bmc1_pre_inst_state                   false
% 35.59/5.00  --bmc1_pre_inst_reach_state             false
% 35.59/5.00  --bmc1_out_unsat_core                   false
% 35.59/5.00  --bmc1_aig_witness_out                  false
% 35.59/5.00  --bmc1_verbose                          false
% 35.59/5.00  --bmc1_dump_clauses_tptp                false
% 35.59/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.59/5.00  --bmc1_dump_file                        -
% 35.59/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.59/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.59/5.00  --bmc1_ucm_extend_mode                  1
% 35.59/5.00  --bmc1_ucm_init_mode                    2
% 35.59/5.00  --bmc1_ucm_cone_mode                    none
% 35.59/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.59/5.00  --bmc1_ucm_relax_model                  4
% 35.59/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.59/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.59/5.00  --bmc1_ucm_layered_model                none
% 35.59/5.00  --bmc1_ucm_max_lemma_size               10
% 35.59/5.00  
% 35.59/5.00  ------ AIG Options
% 35.59/5.00  
% 35.59/5.00  --aig_mode                              false
% 35.59/5.00  
% 35.59/5.00  ------ Instantiation Options
% 35.59/5.00  
% 35.59/5.00  --instantiation_flag                    true
% 35.59/5.00  --inst_sos_flag                         false
% 35.59/5.00  --inst_sos_phase                        true
% 35.59/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.59/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.59/5.00  --inst_lit_sel_side                     num_symb
% 35.59/5.00  --inst_solver_per_active                1400
% 35.59/5.00  --inst_solver_calls_frac                1.
% 35.59/5.00  --inst_passive_queue_type               priority_queues
% 35.59/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.59/5.00  --inst_passive_queues_freq              [25;2]
% 35.59/5.00  --inst_dismatching                      true
% 35.59/5.00  --inst_eager_unprocessed_to_passive     true
% 35.59/5.00  --inst_prop_sim_given                   true
% 35.59/5.00  --inst_prop_sim_new                     false
% 35.59/5.00  --inst_subs_new                         false
% 35.59/5.00  --inst_eq_res_simp                      false
% 35.59/5.00  --inst_subs_given                       false
% 35.59/5.00  --inst_orphan_elimination               true
% 35.59/5.00  --inst_learning_loop_flag               true
% 35.59/5.00  --inst_learning_start                   3000
% 35.59/5.00  --inst_learning_factor                  2
% 35.59/5.00  --inst_start_prop_sim_after_learn       3
% 35.59/5.00  --inst_sel_renew                        solver
% 35.59/5.00  --inst_lit_activity_flag                true
% 35.59/5.00  --inst_restr_to_given                   false
% 35.59/5.00  --inst_activity_threshold               500
% 35.59/5.00  --inst_out_proof                        true
% 35.59/5.00  
% 35.59/5.00  ------ Resolution Options
% 35.59/5.00  
% 35.59/5.00  --resolution_flag                       true
% 35.59/5.00  --res_lit_sel                           adaptive
% 35.59/5.00  --res_lit_sel_side                      none
% 35.59/5.00  --res_ordering                          kbo
% 35.59/5.00  --res_to_prop_solver                    active
% 35.59/5.00  --res_prop_simpl_new                    false
% 35.59/5.00  --res_prop_simpl_given                  true
% 35.59/5.00  --res_passive_queue_type                priority_queues
% 35.59/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.59/5.00  --res_passive_queues_freq               [15;5]
% 35.59/5.00  --res_forward_subs                      full
% 35.59/5.00  --res_backward_subs                     full
% 35.59/5.00  --res_forward_subs_resolution           true
% 35.59/5.00  --res_backward_subs_resolution          true
% 35.59/5.00  --res_orphan_elimination                true
% 35.59/5.00  --res_time_limit                        2.
% 35.59/5.00  --res_out_proof                         true
% 35.59/5.00  
% 35.59/5.00  ------ Superposition Options
% 35.59/5.00  
% 35.59/5.00  --superposition_flag                    true
% 35.59/5.00  --sup_passive_queue_type                priority_queues
% 35.59/5.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.59/5.00  --sup_passive_queues_freq               [1;4]
% 35.59/5.00  --demod_completeness_check              fast
% 35.59/5.00  --demod_use_ground                      true
% 35.59/5.00  --sup_to_prop_solver                    passive
% 35.59/5.00  --sup_prop_simpl_new                    true
% 35.59/5.00  --sup_prop_simpl_given                  true
% 35.59/5.00  --sup_fun_splitting                     false
% 35.59/5.00  --sup_smt_interval                      50000
% 35.59/5.00  
% 35.59/5.00  ------ Superposition Simplification Setup
% 35.59/5.00  
% 35.59/5.00  --sup_indices_passive                   []
% 35.59/5.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.59/5.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.59/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 35.59/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.59/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.59/5.00  --sup_full_bw                           [BwDemod]
% 35.59/5.00  --sup_immed_triv                        [TrivRules]
% 35.59/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.59/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.59/5.00  --sup_immed_bw_main                     []
% 35.59/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.59/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.59/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 35.59/5.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 35.59/5.00  
% 35.59/5.00  ------ Combination Options
% 35.59/5.00  
% 35.59/5.00  --comb_res_mult                         3
% 35.59/5.00  --comb_sup_mult                         2
% 35.59/5.00  --comb_inst_mult                        10
% 35.59/5.00  
% 35.59/5.00  ------ Debug Options
% 35.59/5.00  
% 35.59/5.00  --dbg_backtrace                         false
% 35.59/5.00  --dbg_dump_prop_clauses                 false
% 35.59/5.00  --dbg_dump_prop_clauses_file            -
% 35.59/5.00  --dbg_out_stat                          false
% 35.59/5.00  
% 35.59/5.00  
% 35.59/5.00  
% 35.59/5.00  
% 35.59/5.00  ------ Proving...
% 35.59/5.00  
% 35.59/5.00  
% 35.59/5.00  % SZS status Theorem for theBenchmark.p
% 35.59/5.00  
% 35.59/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.59/5.00  
% 35.59/5.00  fof(f22,conjecture,(
% 35.59/5.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f23,negated_conjecture,(
% 35.59/5.00    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 35.59/5.00    inference(negated_conjecture,[],[f22])).
% 35.59/5.00  
% 35.59/5.00  fof(f36,plain,(
% 35.59/5.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f23])).
% 35.59/5.00  
% 35.59/5.00  fof(f39,plain,(
% 35.59/5.00    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 35.59/5.00    introduced(choice_axiom,[])).
% 35.59/5.00  
% 35.59/5.00  fof(f40,plain,(
% 35.59/5.00    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 35.59/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f39])).
% 35.59/5.00  
% 35.59/5.00  fof(f66,plain,(
% 35.59/5.00    v1_relat_1(sK0)),
% 35.59/5.00    inference(cnf_transformation,[],[f40])).
% 35.59/5.00  
% 35.59/5.00  fof(f1,axiom,(
% 35.59/5.00    v1_xboole_0(k1_xboole_0)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f41,plain,(
% 35.59/5.00    v1_xboole_0(k1_xboole_0)),
% 35.59/5.00    inference(cnf_transformation,[],[f1])).
% 35.59/5.00  
% 35.59/5.00  fof(f13,axiom,(
% 35.59/5.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f27,plain,(
% 35.59/5.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f13])).
% 35.59/5.00  
% 35.59/5.00  fof(f55,plain,(
% 35.59/5.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f27])).
% 35.59/5.00  
% 35.59/5.00  fof(f15,axiom,(
% 35.59/5.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f29,plain,(
% 35.59/5.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 35.59/5.00    inference(ennf_transformation,[],[f15])).
% 35.59/5.00  
% 35.59/5.00  fof(f30,plain,(
% 35.59/5.00    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 35.59/5.00    inference(flattening,[],[f29])).
% 35.59/5.00  
% 35.59/5.00  fof(f57,plain,(
% 35.59/5.00    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f30])).
% 35.59/5.00  
% 35.59/5.00  fof(f17,axiom,(
% 35.59/5.00    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f32,plain,(
% 35.59/5.00    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f17])).
% 35.59/5.00  
% 35.59/5.00  fof(f59,plain,(
% 35.59/5.00    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f32])).
% 35.59/5.00  
% 35.59/5.00  fof(f12,axiom,(
% 35.59/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f54,plain,(
% 35.59/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 35.59/5.00    inference(cnf_transformation,[],[f12])).
% 35.59/5.00  
% 35.59/5.00  fof(f6,axiom,(
% 35.59/5.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f48,plain,(
% 35.59/5.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f6])).
% 35.59/5.00  
% 35.59/5.00  fof(f7,axiom,(
% 35.59/5.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f49,plain,(
% 35.59/5.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f7])).
% 35.59/5.00  
% 35.59/5.00  fof(f8,axiom,(
% 35.59/5.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f50,plain,(
% 35.59/5.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f8])).
% 35.59/5.00  
% 35.59/5.00  fof(f9,axiom,(
% 35.59/5.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f51,plain,(
% 35.59/5.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f9])).
% 35.59/5.00  
% 35.59/5.00  fof(f68,plain,(
% 35.59/5.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 35.59/5.00    inference(definition_unfolding,[],[f50,f51])).
% 35.59/5.00  
% 35.59/5.00  fof(f69,plain,(
% 35.59/5.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 35.59/5.00    inference(definition_unfolding,[],[f49,f68])).
% 35.59/5.00  
% 35.59/5.00  fof(f70,plain,(
% 35.59/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 35.59/5.00    inference(definition_unfolding,[],[f48,f69])).
% 35.59/5.00  
% 35.59/5.00  fof(f71,plain,(
% 35.59/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 35.59/5.00    inference(definition_unfolding,[],[f54,f70])).
% 35.59/5.00  
% 35.59/5.00  fof(f73,plain,(
% 35.59/5.00    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 35.59/5.00    inference(definition_unfolding,[],[f59,f71])).
% 35.59/5.00  
% 35.59/5.00  fof(f21,axiom,(
% 35.59/5.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f64,plain,(
% 35.59/5.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 35.59/5.00    inference(cnf_transformation,[],[f21])).
% 35.59/5.00  
% 35.59/5.00  fof(f19,axiom,(
% 35.59/5.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f34,plain,(
% 35.59/5.00    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f19])).
% 35.59/5.00  
% 35.59/5.00  fof(f62,plain,(
% 35.59/5.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f34])).
% 35.59/5.00  
% 35.59/5.00  fof(f5,axiom,(
% 35.59/5.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f47,plain,(
% 35.59/5.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f5])).
% 35.59/5.00  
% 35.59/5.00  fof(f3,axiom,(
% 35.59/5.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f37,plain,(
% 35.59/5.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.59/5.00    inference(nnf_transformation,[],[f3])).
% 35.59/5.00  
% 35.59/5.00  fof(f38,plain,(
% 35.59/5.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.59/5.00    inference(flattening,[],[f37])).
% 35.59/5.00  
% 35.59/5.00  fof(f45,plain,(
% 35.59/5.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f38])).
% 35.59/5.00  
% 35.59/5.00  fof(f4,axiom,(
% 35.59/5.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f46,plain,(
% 35.59/5.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f4])).
% 35.59/5.00  
% 35.59/5.00  fof(f72,plain,(
% 35.59/5.00    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 35.59/5.00    inference(definition_unfolding,[],[f46,f71])).
% 35.59/5.00  
% 35.59/5.00  fof(f11,axiom,(
% 35.59/5.00    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f26,plain,(
% 35.59/5.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f11])).
% 35.59/5.00  
% 35.59/5.00  fof(f53,plain,(
% 35.59/5.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f26])).
% 35.59/5.00  
% 35.59/5.00  fof(f2,axiom,(
% 35.59/5.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f24,plain,(
% 35.59/5.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f2])).
% 35.59/5.00  
% 35.59/5.00  fof(f42,plain,(
% 35.59/5.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f24])).
% 35.59/5.00  
% 35.59/5.00  fof(f14,axiom,(
% 35.59/5.00    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f28,plain,(
% 35.59/5.00    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f14])).
% 35.59/5.00  
% 35.59/5.00  fof(f56,plain,(
% 35.59/5.00    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f28])).
% 35.59/5.00  
% 35.59/5.00  fof(f20,axiom,(
% 35.59/5.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f35,plain,(
% 35.59/5.00    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f20])).
% 35.59/5.00  
% 35.59/5.00  fof(f63,plain,(
% 35.59/5.00    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f35])).
% 35.59/5.00  
% 35.59/5.00  fof(f16,axiom,(
% 35.59/5.00    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f31,plain,(
% 35.59/5.00    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f16])).
% 35.59/5.00  
% 35.59/5.00  fof(f58,plain,(
% 35.59/5.00    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f31])).
% 35.59/5.00  
% 35.59/5.00  fof(f18,axiom,(
% 35.59/5.00    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 35.59/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.59/5.00  
% 35.59/5.00  fof(f33,plain,(
% 35.59/5.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 35.59/5.00    inference(ennf_transformation,[],[f18])).
% 35.59/5.00  
% 35.59/5.00  fof(f60,plain,(
% 35.59/5.00    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f33])).
% 35.59/5.00  
% 35.59/5.00  fof(f65,plain,(
% 35.59/5.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 35.59/5.00    inference(cnf_transformation,[],[f21])).
% 35.59/5.00  
% 35.59/5.00  fof(f61,plain,(
% 35.59/5.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 35.59/5.00    inference(cnf_transformation,[],[f33])).
% 35.59/5.00  
% 35.59/5.00  fof(f67,plain,(
% 35.59/5.00    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 35.59/5.00    inference(cnf_transformation,[],[f40])).
% 35.59/5.00  
% 35.59/5.00  cnf(c_21,negated_conjecture,
% 35.59/5.00      ( v1_relat_1(sK0) ),
% 35.59/5.00      inference(cnf_transformation,[],[f66]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_566,plain,
% 35.59/5.00      ( v1_relat_1(sK0) = iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_0,plain,
% 35.59/5.00      ( v1_xboole_0(k1_xboole_0) ),
% 35.59/5.00      inference(cnf_transformation,[],[f41]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_582,plain,
% 35.59/5.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_9,plain,
% 35.59/5.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 35.59/5.00      inference(cnf_transformation,[],[f55]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_575,plain,
% 35.59/5.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1011,plain,
% 35.59/5.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_582,c_575]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_11,plain,
% 35.59/5.00      ( ~ v1_relat_1(X0)
% 35.59/5.00      | ~ v1_relat_1(X1)
% 35.59/5.00      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 35.59/5.00      inference(cnf_transformation,[],[f57]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_573,plain,
% 35.59/5.00      ( v1_relat_1(X0) != iProver_top
% 35.59/5.00      | v1_relat_1(X1) != iProver_top
% 35.59/5.00      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_13,plain,
% 35.59/5.00      ( ~ v1_relat_1(X0)
% 35.59/5.00      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 35.59/5.00      inference(cnf_transformation,[],[f73]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_571,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1766,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 35.59/5.00      | v1_relat_1(X0) != iProver_top
% 35.59/5.00      | v1_relat_1(X1) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_573,c_571]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_8210,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) = k5_relat_1(k1_xboole_0,X0)
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_1011,c_1766]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_105566,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_566,c_8210]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_19,plain,
% 35.59/5.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 35.59/5.00      inference(cnf_transformation,[],[f64]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_16,plain,
% 35.59/5.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 35.59/5.00      | ~ v1_relat_1(X0)
% 35.59/5.00      | ~ v1_relat_1(X1) ),
% 35.59/5.00      inference(cnf_transformation,[],[f62]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_568,plain,
% 35.59/5.00      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 35.59/5.00      | v1_relat_1(X0) != iProver_top
% 35.59/5.00      | v1_relat_1(X1) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1004,plain,
% 35.59/5.00      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 35.59/5.00      | v1_relat_1(X0) != iProver_top
% 35.59/5.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_19,c_568]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_47,plain,
% 35.59/5.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_49,plain,
% 35.59/5.00      ( v1_relat_1(k1_xboole_0) = iProver_top
% 35.59/5.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 35.59/5.00      inference(instantiation,[status(thm)],[c_47]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_66,plain,
% 35.59/5.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1787,plain,
% 35.59/5.00      ( v1_relat_1(X0) != iProver_top
% 35.59/5.00      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top ),
% 35.59/5.00      inference(global_propositional_subsumption,
% 35.59/5.00                [status(thm)],
% 35.59/5.00                [c_1004,c_49,c_66]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1788,plain,
% 35.59/5.00      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) = iProver_top
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(renaming,[status(thm)],[c_1787]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_6,plain,
% 35.59/5.00      ( r1_tarski(k1_xboole_0,X0) ),
% 35.59/5.00      inference(cnf_transformation,[],[f47]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_578,plain,
% 35.59/5.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_2,plain,
% 35.59/5.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 35.59/5.00      inference(cnf_transformation,[],[f45]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_580,plain,
% 35.59/5.00      ( X0 = X1
% 35.59/5.00      | r1_tarski(X0,X1) != iProver_top
% 35.59/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1565,plain,
% 35.59/5.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_578,c_580]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_2641,plain,
% 35.59/5.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_1788,c_1565]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_13444,plain,
% 35.59/5.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_566,c_2641]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_105598,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 35.59/5.00      inference(light_normalisation,[status(thm)],[c_105566,c_13444]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_5,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 35.59/5.00      inference(cnf_transformation,[],[f72]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_8,plain,
% 35.59/5.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 35.59/5.00      inference(cnf_transformation,[],[f53]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_576,plain,
% 35.59/5.00      ( v1_xboole_0(X0) != iProver_top
% 35.59/5.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1,plain,
% 35.59/5.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 35.59/5.00      inference(cnf_transformation,[],[f42]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_581,plain,
% 35.59/5.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1425,plain,
% 35.59/5.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 35.59/5.00      | v1_xboole_0(X0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_576,c_581]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_2844,plain,
% 35.59/5.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_582,c_1425]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_105599,plain,
% 35.59/5.00      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 35.59/5.00      inference(demodulation,[status(thm)],[c_105598,c_5,c_2844]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_10,plain,
% 35.59/5.00      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 35.59/5.00      inference(cnf_transformation,[],[f56]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_574,plain,
% 35.59/5.00      ( v1_relat_1(X0) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_17,plain,
% 35.59/5.00      ( ~ v1_relat_1(X0)
% 35.59/5.00      | ~ v1_relat_1(X1)
% 35.59/5.00      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 35.59/5.00      inference(cnf_transformation,[],[f63]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_567,plain,
% 35.59/5.00      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 35.59/5.00      | v1_relat_1(X1) != iProver_top
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1174,plain,
% 35.59/5.00      ( k5_relat_1(k4_relat_1(k4_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k4_relat_1(X0)))
% 35.59/5.00      | v1_relat_1(X0) != iProver_top
% 35.59/5.00      | v1_relat_1(X1) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_574,c_567]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_2803,plain,
% 35.59/5.00      ( k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_566,c_1174]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_12,plain,
% 35.59/5.00      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 35.59/5.00      inference(cnf_transformation,[],[f58]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_572,plain,
% 35.59/5.00      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1169,plain,
% 35.59/5.00      ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_566,c_572]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_2812,plain,
% 35.59/5.00      ( k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X0))
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(light_normalisation,[status(thm)],[c_2803,c_1169]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_17245,plain,
% 35.59/5.00      ( k4_relat_1(k5_relat_1(k4_relat_1(X0),k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0)))
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_574,c_2812]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_17874,plain,
% 35.59/5.00      ( k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(X0)),k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0))))
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_574,c_17245]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_36859,plain,
% 35.59/5.00      ( k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))) ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_1011,c_17874]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1765,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k2_zfmisc_1(k1_relat_1(k4_relat_1(X0)),k2_relat_1(k4_relat_1(X0))))) = k4_relat_1(X0)
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_574,c_571]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7607,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0))))) = k4_relat_1(k1_xboole_0) ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_1011,c_1765]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_15,plain,
% 35.59/5.00      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 35.59/5.00      inference(cnf_transformation,[],[f60]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_569,plain,
% 35.59/5.00      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1917,plain,
% 35.59/5.00      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_1011,c_569]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_18,plain,
% 35.59/5.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 35.59/5.00      inference(cnf_transformation,[],[f65]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1927,plain,
% 35.59/5.00      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 35.59/5.00      inference(light_normalisation,[status(thm)],[c_1917,c_18]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_14,plain,
% 35.59/5.00      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 35.59/5.00      inference(cnf_transformation,[],[f61]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_570,plain,
% 35.59/5.00      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1916,plain,
% 35.59/5.00      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_1011,c_570]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1930,plain,
% 35.59/5.00      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 35.59/5.00      inference(light_normalisation,[status(thm)],[c_1916,c_19]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7625,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = k4_relat_1(k1_xboole_0) ),
% 35.59/5.00      inference(light_normalisation,[status(thm)],[c_7607,c_1927,c_1930]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7626,plain,
% 35.59/5.00      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 35.59/5.00      inference(demodulation,[status(thm)],[c_7625,c_5,c_2844]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1919,plain,
% 35.59/5.00      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 35.59/5.00      | v1_relat_1(X0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_1011,c_567]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_6299,plain,
% 35.59/5.00      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_566,c_1919]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7653,plain,
% 35.59/5.00      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 35.59/5.00      inference(demodulation,[status(thm)],[c_7626,c_6299]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7883,plain,
% 35.59/5.00      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 35.59/5.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_7653,c_573]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_22,plain,
% 35.59/5.00      ( v1_relat_1(sK0) = iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_44,plain,
% 35.59/5.00      ( v1_relat_1(X0) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_46,plain,
% 35.59/5.00      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 35.59/5.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 35.59/5.00      inference(instantiation,[status(thm)],[c_44]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_6677,plain,
% 35.59/5.00      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_6299,c_573]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_19422,plain,
% 35.59/5.00      ( v1_relat_1(k4_relat_1(sK0)) | ~ v1_relat_1(sK0) ),
% 35.59/5.00      inference(instantiation,[status(thm)],[c_10]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_19423,plain,
% 35.59/5.00      ( v1_relat_1(k4_relat_1(sK0)) = iProver_top
% 35.59/5.00      | v1_relat_1(sK0) != iProver_top ),
% 35.59/5.00      inference(predicate_to_equality,[status(thm)],[c_19422]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_28020,plain,
% 35.59/5.00      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 35.59/5.00      inference(global_propositional_subsumption,
% 35.59/5.00                [status(thm)],
% 35.59/5.00                [c_7883,c_22,c_46,c_49,c_66,c_6677,c_19423]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_28075,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_28020,c_571]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_1566,plain,
% 35.59/5.00      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 35.59/5.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 35.59/5.00      | v1_relat_1(X0) != iProver_top
% 35.59/5.00      | v1_relat_1(X1) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_568,c_580]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7882,plain,
% 35.59/5.00      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_relat_1(k1_xboole_0)
% 35.59/5.00      | r1_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 35.59/5.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_7653,c_1566]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7904,plain,
% 35.59/5.00      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 35.59/5.00      | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 35.59/5.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 35.59/5.00      inference(light_normalisation,[status(thm)],[c_7882,c_19,c_7653]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_6676,plain,
% 35.59/5.00      ( k1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0))) = k1_relat_1(k4_relat_1(k1_xboole_0))
% 35.59/5.00      | r1_tarski(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_6299,c_1566]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_6696,plain,
% 35.59/5.00      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 35.59/5.00      | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 35.59/5.00      inference(light_normalisation,[status(thm)],[c_6676,c_1927,c_6299]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7913,plain,
% 35.59/5.00      ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 35.59/5.00      | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 35.59/5.00      | k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 35.59/5.00      inference(global_propositional_subsumption,
% 35.59/5.00                [status(thm)],
% 35.59/5.00                [c_7904,c_46,c_49,c_66,c_6696]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7914,plain,
% 35.59/5.00      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 35.59/5.00      | r1_tarski(k1_xboole_0,k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))) != iProver_top
% 35.59/5.00      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 35.59/5.00      inference(renaming,[status(thm)],[c_7913]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7920,plain,
% 35.59/5.00      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 35.59/5.00      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 35.59/5.00      inference(forward_subsumption_resolution,
% 35.59/5.00                [status(thm)],
% 35.59/5.00                [c_7914,c_578]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_7922,plain,
% 35.59/5.00      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0
% 35.59/5.00      | v1_relat_1(sK0) != iProver_top ),
% 35.59/5.00      inference(superposition,[status(thm)],[c_574,c_7920]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_8177,plain,
% 35.59/5.00      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 35.59/5.00      inference(global_propositional_subsumption,
% 35.59/5.00                [status(thm)],
% 35.59/5.00                [c_7922,c_22]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_28085,plain,
% 35.59/5.00      ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 35.59/5.00      inference(light_normalisation,[status(thm)],[c_28075,c_8177]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_28086,plain,
% 35.59/5.00      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 35.59/5.00      inference(demodulation,[status(thm)],[c_28085,c_5,c_2844]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_28559,plain,
% 35.59/5.00      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k1_xboole_0 ),
% 35.59/5.00      inference(demodulation,[status(thm)],[c_28086,c_7653]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_36878,plain,
% 35.59/5.00      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 35.59/5.00      inference(light_normalisation,
% 35.59/5.00                [status(thm)],
% 35.59/5.00                [c_36859,c_7626,c_28559]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_20,negated_conjecture,
% 35.59/5.00      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 35.59/5.00      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 35.59/5.00      inference(cnf_transformation,[],[f67]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_36906,plain,
% 35.59/5.00      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 35.59/5.00      | k1_xboole_0 != k1_xboole_0 ),
% 35.59/5.00      inference(demodulation,[status(thm)],[c_36878,c_20]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(c_36907,plain,
% 35.59/5.00      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
% 35.59/5.00      inference(equality_resolution_simp,[status(thm)],[c_36906]) ).
% 35.59/5.00  
% 35.59/5.00  cnf(contradiction,plain,
% 35.59/5.00      ( $false ),
% 35.59/5.00      inference(minisat,[status(thm)],[c_105599,c_36907]) ).
% 35.59/5.00  
% 35.59/5.00  
% 35.59/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.59/5.00  
% 35.59/5.00  ------                               Statistics
% 35.59/5.00  
% 35.59/5.00  ------ Selected
% 35.59/5.00  
% 35.59/5.00  total_time:                             4.126
% 35.59/5.00  
%------------------------------------------------------------------------------
